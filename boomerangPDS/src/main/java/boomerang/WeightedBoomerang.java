/**
 * ***************************************************************************** Copyright (c) 2018
 * Fraunhofer IEM, Paderborn, Germany. This program and the accompanying materials are made
 * available under the terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *
 * <p>SPDX-License-Identifier: EPL-2.0
 *
 * <p>Contributors: Johannes Spaeth - initial API and implementation
 * *****************************************************************************
 */
package boomerang;

import boomerang.BoomerangOptions.ArrayStrategy;
import boomerang.callgraph.BackwardsObservableICFG;
import boomerang.callgraph.ObservableDynamicICFG;
import boomerang.callgraph.ObservableICFG;
import boomerang.callgraph.ObservableStaticICFG;
import boomerang.controlflowgraph.DynamicCFG;
import boomerang.controlflowgraph.ObservableControlFlowGraph;
import boomerang.controlflowgraph.PredecessorListener;
import boomerang.controlflowgraph.StaticCFG;
import boomerang.controlflowgraph.SuccessorListener;
import boomerang.debugger.Debugger;
import boomerang.poi.AbstractPOI;
import boomerang.poi.CopyAccessPathChain;
import boomerang.poi.ExecuteImportFieldStmtPOI;
import boomerang.poi.PointOfIndirection;
import boomerang.results.BackwardBoomerangResults;
import boomerang.results.ForwardBoomerangResults;
import boomerang.scene.AllocVal;
import boomerang.scene.CallGraph;
import boomerang.scene.ControlFlowGraph;
import boomerang.scene.ControlFlowGraph.Edge;
import boomerang.scene.DataFlowScope;
import boomerang.scene.Field;
import boomerang.scene.Field.ArrayField;
import boomerang.scene.Method;
import boomerang.scene.Pair;
import boomerang.scene.Statement;
import boomerang.scene.StaticFieldVal;
import boomerang.scene.Val;
import boomerang.scene.jimple.JimpleField;
import boomerang.scene.jimple.JimpleMethod;
import boomerang.scene.jimple.JimpleStaticFieldVal;
import boomerang.solver.AbstractBoomerangSolver;
import boomerang.solver.BackwardBoomerangSolver;
import boomerang.solver.ControlFlowEdgeBasedFieldTransitionListener;
import boomerang.solver.ForwardBoomerangSolver;
import boomerang.stats.IBoomerangStats;
import boomerang.util.DefaultValueMap;
import com.google.common.base.Stopwatch;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;
import com.google.common.collect.Table.Cell;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.SootMethod;
import sync.pds.solver.SyncPDSSolver.PDSSystem;
import sync.pds.solver.WeightFunctions;
import sync.pds.solver.nodes.GeneratedState;
import sync.pds.solver.nodes.INode;
import sync.pds.solver.nodes.Node;
import sync.pds.solver.nodes.NodeWithLocation;
import sync.pds.solver.nodes.PopNode;
import sync.pds.solver.nodes.PushNode;
import sync.pds.solver.nodes.SingleNode;
import wpds.impl.NestedWeightedPAutomatons;
import wpds.impl.Rule;
import wpds.impl.SummaryNestedWeightedPAutomatons;
import wpds.impl.Transition;
import wpds.impl.Weight;
import wpds.impl.WeightedPAutomaton;
import wpds.interfaces.WPAStateListener;

public abstract class WeightedBoomerang<W extends Weight> {
  protected ObservableICFG<Statement, Method> icfg;
  protected ObservableControlFlowGraph cfg;
  private static final Logger LOGGER = LoggerFactory.getLogger(WeightedBoomerang.class);
  private Map<Entry<INode<Node<Edge, Val>>, Field>, INode<Node<Edge, Val>>> genField =
      new HashMap<>();
  private long lastTick;
  private IBoomerangStats<W> stats;
  private Set<Method> visitedMethods = Sets.newHashSet();
  private Set<SolverCreationListener<W>> solverCreationListeners = Sets.newHashSet();
  private Multimap<SolverPair, ExecuteImportFieldStmtPOI<W>> poiListeners = HashMultimap.create();
  private Multimap<SolverPair, INode<Node<Edge, Val>>> activatedPoi = HashMultimap.create();
  private final DefaultValueMap<ForwardQuery, ForwardBoomerangSolver<W>> queryToSolvers =
      new DefaultValueMap<ForwardQuery, ForwardBoomerangSolver<W>>() {
        @Override
        protected ForwardBoomerangSolver<W> createItem(final ForwardQuery key) {
          final ForwardBoomerangSolver<W> solver;
          LOGGER.trace("Forward solving query: {}", key);
          forwardQueries++;
          solver = createForwardSolver(key);

          stats.registerSolver(key, solver);
          solver.getCallAutomaton().registerListener((t, w, aut) -> checkTimeout());
          solver.getFieldAutomaton().registerListener((t, w, aut) -> checkTimeout());
          onCreateSubSolver(key, solver);
          return solver;
        }
      };
  private int forwardQueries;
  private int backwardQueries;
  private final QueryGraph<W> queryGraph;
  private final DefaultValueMap<BackwardQuery, BackwardBoomerangSolver<W>> queryToBackwardSolvers =
      new DefaultValueMap<BackwardQuery, BackwardBoomerangSolver<W>>() {
        @Override
        protected BackwardBoomerangSolver<W> createItem(BackwardQuery key) {

          if (backwardSolverIns != null) return backwardSolverIns;
          BackwardBoomerangSolver<W> backwardSolver =
              new BackwardBoomerangSolver<W>(
                  bwicfg(),
                  cfg(),
                  genField,
                  key,
                  WeightedBoomerang.this.options,
                  createCallSummaries(null, backwardCallSummaries),
                  createFieldSummaries(null, backwardFieldSummaries),
                  WeightedBoomerang.this.dataFlowscope,
                  options.getBackwardFlowFunction(),
                  callGraph.getFieldLoadStatements(),
                  callGraph.getFieldStoreStatements(),
                  null) {

                @Override
                public WeightFunctions<ControlFlowGraph.Edge, Val, Field, W> getFieldWeights() {
                  return WeightedBoomerang.this.getBackwardFieldWeights();
                }

                @Override
                public WeightFunctions<ControlFlowGraph.Edge, Val, ControlFlowGraph.Edge, W>
                    getCallWeights() {
                  return WeightedBoomerang.this.getBackwardCallWeights();
                }

                @Override
                protected boolean forceUnbalanced(INode<Val> node, Collection<INode<Val>> sources) {
                  return sources.contains(rootQuery) && callAutomaton.isUnbalancedState(node);
                }

                @Override
                protected boolean preventCallTransitionAdd(
                    Transition<ControlFlowGraph.Edge, INode<Val>> t, W weight) {
                  checkTimeout();
                  return super.preventCallTransitionAdd(t, weight);
                }

                @Override
                protected boolean preventFieldTransitionAdd(
                    Transition<Field, INode<Node<ControlFlowGraph.Edge, Val>>> t, W weight) {
                  checkTimeout();
                  return super.preventFieldTransitionAdd(t, weight);
                }
              };
          backwardSolver.registerListener(
              node -> {
                Optional<AllocVal> allocNode = isAllocationNode(node.stmt(), node.fact());
                if (allocNode.isPresent()
                    || node.stmt().getTarget().isArrayLoad()
                    || node.stmt().getTarget().isFieldLoad()) {
                  backwardSolver
                      .getFieldAutomaton()
                      .registerListener(new EmptyFieldListener(key, node));
                }
                addVisitedMethod(node.stmt().getStart().getMethod());

                handleMapsBackward(node);

                if (options.trackStaticFieldAtEntryPointToClinit()) {
                  handleStaticInitializer(node, backwardSolver);
                }
              });
          backwardSolverIns = backwardSolver;
          return backwardSolver;
        }
      };

  private void handleStaticInitializer(
      Node<Edge, Val> node, BackwardBoomerangSolver<W> backwardSolver) {
    if (options.trackStaticFieldAtEntryPointToClinit()
        && node.fact().isStatic()
        && isFirstStatementOfEntryPoint(node.stmt().getStart())) {
      Val fact = node.fact();
      if (fact instanceof JimpleStaticFieldVal) {
        JimpleStaticFieldVal val = ((JimpleStaticFieldVal) fact);
        for (SootMethod m :
            ((JimpleField) val.field()).getSootField().getDeclaringClass().getMethods()) {
          if (!m.hasActiveBody()) {
            continue;
          }
          JimpleMethod jimpleMethod = JimpleMethod.of(m);
          if (m.isStaticInitializer()) {
            for (Statement ep : icfg().getEndPointsOf(JimpleMethod.of(m))) {
              StaticFieldVal newVal =
                  new JimpleStaticFieldVal(((JimpleField) val.field()), jimpleMethod);
              cfg.addPredsOfListener(
                  new PredecessorListener(ep) {
                    @Override
                    public void getPredecessor(Statement pred) {
                      backwardSolver.addNormalCallFlow(
                          node, new Node<>(new Edge(pred, ep), newVal));
                      backwardSolver.addNormalFieldFlow(
                          node, new Node<>(new Edge(pred, ep), newVal));
                    }
                  });
            }
          }
        }
      }
    }
  }

  protected boolean isFirstStatementOfEntryPoint(Statement stmt) {
    return callGraph.getEntryPoints().contains(stmt.getMethod())
        && stmt.getMethod().getControlFlowGraph().getStartPoints().contains(stmt);
  }

  private static final String MAP_PUT_SUB_SIGNATURE = "java.util.Map: java.lang.Object put(";
  private static final String MAP_GET_SUB_SIGNATURE = "java.util.Map: java.lang.Object get(";

  protected void handleMapsBackward(Node<Edge, Val> node) {
    Statement rstmt = node.stmt().getStart();
    if (rstmt.isAssign()
        && rstmt.containsInvokeExpr()
        && rstmt.getInvokeExpr().toString().contains(MAP_GET_SUB_SIGNATURE)) {
      if (rstmt.getLeftOp().equals(node.fact())) {

        cfg.addPredsOfListener(
            new PredecessorListener(rstmt) {
              @Override
              public void getPredecessor(Statement pred) {
                BackwardQuery bwq =
                    BackwardQuery.make(new Edge(pred, rstmt), rstmt.getInvokeExpr().getArg(0));
                backwardSolve(bwq);
                for (ForwardQuery q : Lists.newArrayList(queryToSolvers.keySet())) {
                  if (queryToSolvers.get(q).getReachedStates().contains(bwq.asNode())) {
                    Val var = q.var();
                    AllocVal v = (AllocVal) var;
                    if (v.getAllocVal().isStringConstant()) {
                      String key = v.getAllocVal().getStringValue();
                      backwardSolverIns.propagate(
                          node,
                          new PushNode<>(
                              new Edge(pred, rstmt),
                              rstmt.getInvokeExpr().getBase(),
                              Field.string(key),
                              PDSSystem.FIELDS));
                    }
                  }
                }
              }
            });
      }
    }
    if (rstmt.containsInvokeExpr()
        && rstmt.getInvokeExpr().toString().contains(MAP_PUT_SUB_SIGNATURE)) {
      if (rstmt.getInvokeExpr().getBase().equals(node.fact())) {
        cfg.addPredsOfListener(
            new PredecessorListener(rstmt) {
              @Override
              public void getPredecessor(Statement pred) {
                BackwardQuery bwq =
                    BackwardQuery.make(new Edge(pred, rstmt), rstmt.getInvokeExpr().getArg(0));
                backwardSolve(bwq);
                for (ForwardQuery q : Lists.newArrayList(queryToSolvers.keySet())) {
                  if (queryToSolvers.get(q).getReachedStates().contains(bwq.asNode())) {
                    Val var = q.var();
                    AllocVal v = (AllocVal) var;

                    if (v.getAllocVal().isStringConstant()) {
                      String key = v.getAllocVal().getStringValue();
                      NodeWithLocation<Edge, Val, Field> succNode =
                          new NodeWithLocation<>(
                              new Edge(pred, rstmt),
                              rstmt.getInvokeExpr().getArg(1),
                              Field.string(key));
                      backwardSolverIns.propagate(node, new PopNode<>(succNode, PDSSystem.FIELDS));
                    }
                  }
                }
              }
            });
      }
    }
  }

  protected void handleMapsForward(ForwardBoomerangSolver<W> solver, Node<Edge, Val> node) {
    Statement rstmt = node.stmt().getTarget();
    if (rstmt.containsInvokeExpr()) {
      if (rstmt.isAssign() && rstmt.getInvokeExpr().toString().contains(MAP_GET_SUB_SIGNATURE)) {
        if (rstmt.getInvokeExpr().getBase().equals(node.fact())) {
          BackwardQuery bwq = BackwardQuery.make(node.stmt(), rstmt.getInvokeExpr().getArg(0));
          backwardSolve(bwq);
          cfg.addSuccsOfListener(
              new SuccessorListener(rstmt) {
                @Override
                public void getSuccessor(Statement succ) {
                  for (ForwardQuery q : Lists.newArrayList(queryToSolvers.keySet())) {
                    if (queryToSolvers.get(q).getReachedStates().contains(bwq.asNode())) {
                      Val var = q.var();
                      AllocVal v = (AllocVal) var;

                      if (v.getAllocVal().isStringConstant()) {
                        String key = v.getAllocVal().getStringValue();
                        NodeWithLocation<Edge, Val, Field> succNode =
                            new NodeWithLocation<>(
                                new Edge(rstmt, succ), rstmt.getLeftOp(), Field.string(key));
                        solver.propagate(node, new PopNode<>(succNode, PDSSystem.FIELDS));
                      }
                    }
                  }
                }
              });
        }
      }
      if (rstmt.getInvokeExpr().toString().contains(MAP_PUT_SUB_SIGNATURE)) {
        if (rstmt.getInvokeExpr().getArg(1).equals(node.fact())) {

          BackwardQuery bwq = BackwardQuery.make(node.stmt(), rstmt.getInvokeExpr().getArg(0));
          backwardSolve(bwq);
          cfg.addSuccsOfListener(
              new SuccessorListener(rstmt) {
                @Override
                public void getSuccessor(Statement succ) {
                  for (ForwardQuery q : Lists.newArrayList(queryToSolvers.keySet())) {
                    if (queryToSolvers.get(q).getReachedStates().contains(bwq.asNode())) {
                      Val var = q.var();
                      AllocVal v = (AllocVal) var;
                      if (v.getAllocVal().isStringConstant()) {
                        String key = v.getAllocVal().getStringValue();
                        solver.propagate(
                            node,
                            new PushNode<>(
                                new Edge(rstmt, succ),
                                rstmt.getInvokeExpr().getBase(),
                                Field.string(key),
                                PDSSystem.FIELDS));
                      }
                    }
                  }
                }
              });
        }
      }
    }
  }

  private BackwardBoomerangSolver<W> backwardSolverIns;
  private boolean solving;

  public void checkTimeout() {
    if (options.analysisTimeoutMS() > 0) {
      long elapsed = analysisWatch.elapsed(TimeUnit.MILLISECONDS);
      if (elapsed - lastTick > 15000) {
        LOGGER.debug(
            "Elapsed Time: {}/{}, Visited Methods {}",
            elapsed,
            options.analysisTimeoutMS(),
            visitedMethods.size());
        LOGGER.debug("Forward / Backward Queries: {}/{}", forwardQueries, backwardQueries);

        if (LOGGER.isDebugEnabled()) {
          printElapsedTimes();
          printRules();
          printStats();
        }
        lastTick = elapsed;
      }
      if (options.analysisTimeoutMS() < elapsed) {
        if (analysisWatch.isRunning()) analysisWatch.stop();
        throw new BoomerangTimeoutException(elapsed, stats);
      }
    }
  }

  private ObservableICFG<Statement, Method> bwicfg;
  private NestedWeightedPAutomatons<Edge, INode<Val>, W> backwardCallSummaries =
      new SummaryNestedWeightedPAutomatons<>();
  private NestedWeightedPAutomatons<Field, INode<Node<Edge, Val>>, W> backwardFieldSummaries =
      new SummaryNestedWeightedPAutomatons<>();
  private NestedWeightedPAutomatons<Edge, INode<Val>, W> forwardCallSummaries =
      new SummaryNestedWeightedPAutomatons<>();
  private NestedWeightedPAutomatons<Field, INode<Node<Edge, Val>>, W> forwardFieldSummaries =
      new SummaryNestedWeightedPAutomatons<>();
  private DefaultValueMap<FieldWritePOI, FieldWritePOI> fieldWrites =
      new DefaultValueMap<FieldWritePOI, FieldWritePOI>() {
        @Override
        protected FieldWritePOI createItem(FieldWritePOI key) {
          stats.registerFieldWritePOI(key);
          return key;
        }
      };
  protected final BoomerangOptions options;
  private Stopwatch analysisWatch = Stopwatch.createUnstarted();
  private final DataFlowScope dataFlowscope;
  private CallGraph callGraph;
  private INode<Val> rootQuery;

  public WeightedBoomerang(CallGraph cg, DataFlowScope scope, BoomerangOptions options) {
    this.options = options;
    this.options.checkValid();
    this.stats = options.statsFactory();
    this.dataFlowscope = scope;

    if (options.onTheFlyControlFlow()) {
      this.cfg = new DynamicCFG();
    } else {
      this.cfg = new StaticCFG();
    }

    if (options.onTheFlyCallGraph()) {
      icfg = new ObservableDynamicICFG(cfg, options.getResolutionStrategy().newInstance(this, cg));
    } else {
      icfg = new ObservableStaticICFG(cg);
    }
    this.callGraph = cg;
    this.queryGraph = new QueryGraph<>(this);
  }

  public WeightedBoomerang(CallGraph cg, DataFlowScope scope) {
    this(cg, scope, new DefaultBoomerangOptions());
  }

  protected void addVisitedMethod(Method method) {
    if (!dataFlowscope.isExcluded(method) && visitedMethods.add(method)) {
      LOGGER.trace("Reach Method: {}", method);
    }
  }

  protected Optional<AllocVal> isAllocationNode(ControlFlowGraph.Edge s, Val fact) {
    return options.getAllocationVal(s.getStart().getMethod(), s.getStart(), fact);
  }

  protected ForwardBoomerangSolver<W> createForwardSolver(final ForwardQuery sourceQuery) {
    final ForwardBoomerangSolver<W> solver =
        new ForwardBoomerangSolver<W>(
            icfg(),
            cfg(),
            sourceQuery,
            genField,
            options,
            createCallSummaries(sourceQuery, forwardCallSummaries),
            createFieldSummaries(sourceQuery, forwardFieldSummaries),
            dataFlowscope,
            options.getForwardFlowFunctions(),
            callGraph.getFieldLoadStatements(),
            callGraph.getFieldStoreStatements(),
            sourceQuery.getType()) {

          @Override
          public WeightFunctions<ControlFlowGraph.Edge, Val, ControlFlowGraph.Edge, W>
              getCallWeights() {
            return WeightedBoomerang.this.getForwardCallWeights(sourceQuery);
          }

          @Override
          public WeightFunctions<ControlFlowGraph.Edge, Val, Field, W> getFieldWeights() {
            return WeightedBoomerang.this.getForwardFieldWeights();
          }

          @Override
          public void addCallRule(Rule<ControlFlowGraph.Edge, INode<Val>, W> rule) {
            if (preventCallRuleAdd(sourceQuery, rule)) {
              return;
            }
            super.addCallRule(rule);
          }

          @Override
          protected boolean forceUnbalanced(INode<Val> node, Collection<INode<Val>> sources) {
            return queryGraph.isRoot(sourceQuery);
          }

          @Override
          protected void overwriteFieldAtStatement(
              Edge fieldWriteStatement,
              Transition<Field, INode<Node<Edge, Val>>> killedTransition) {
            BackwardQuery backwardQuery =
                BackwardQuery.make(
                    killedTransition.getTarget().fact().stmt(),
                    fieldWriteStatement.getTarget().getRightOp());
            CopyAccessPathChain<W> copyAccessPathChain =
                new CopyAccessPathChain<>(
                    queryToSolvers.get(sourceQuery),
                    queryToBackwardSolvers.getOrCreate(backwardQuery),
                    fieldWriteStatement,
                    killedTransition);
            copyAccessPathChain.exec();
            queryGraph.addEdge(sourceQuery, killedTransition.getStart().fact(), backwardQuery);
          }

          @Override
          protected boolean preventCallTransitionAdd(
              Transition<ControlFlowGraph.Edge, INode<Val>> t, W weight) {
            checkTimeout();
            return super.preventCallTransitionAdd(t, weight);
          }

          @Override
          protected boolean preventFieldTransitionAdd(
              Transition<Field, INode<Node<ControlFlowGraph.Edge, Val>>> t, W weight) {
            checkTimeout();
            return super.preventFieldTransitionAdd(t, weight);
          }
        };

    solver.registerListener(
        node -> {
          if (node.stmt().getStart().isFieldStore()) {
            forwardHandleFieldWrite(node, createFieldStore(node.stmt()), sourceQuery);
          } else if (options.getArrayStrategy() != ArrayStrategy.DISABLED
              && node.stmt().getStart().isArrayStore()) {
            forwardHandleFieldWrite(node, createArrayFieldStore(node.stmt()), sourceQuery);
          }

          addVisitedMethod(node.stmt().getStart().getMethod());
          handleMapsForward(solver, node);
        });

    return solver;
  }

  private NestedWeightedPAutomatons<ControlFlowGraph.Edge, INode<Val>, W> createCallSummaries(
      final ForwardQuery sourceQuery,
      final NestedWeightedPAutomatons<ControlFlowGraph.Edge, INode<Val>, W> summaries) {
    return new NestedWeightedPAutomatons<ControlFlowGraph.Edge, INode<Val>, W>() {

      @Override
      public void putSummaryAutomaton(
          INode<Val> target, WeightedPAutomaton<ControlFlowGraph.Edge, INode<Val>, W> aut) {
        summaries.putSummaryAutomaton(target, aut);
      }

      @Override
      public WeightedPAutomaton<ControlFlowGraph.Edge, INode<Val>, W> getSummaryAutomaton(
          INode<Val> target) {
        if (sourceQuery.var() instanceof AllocVal) {
          AllocVal allocVal = (AllocVal) sourceQuery.var();
          Val f;
          if (target.fact().isUnbalanced()) {
            f = target.fact().asUnbalanced(null);
          } else {
            f = target.fact();
          }
          if (f.equals(allocVal.getDelegate())) {
            return queryToSolvers.getOrCreate(sourceQuery).getCallAutomaton();
          }
        }
        return summaries.getSummaryAutomaton(target);
      }
    };
  }

  private NestedWeightedPAutomatons<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W>
      createFieldSummaries(
          final ForwardQuery sourceQuery,
          final NestedWeightedPAutomatons<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W>
              summaries) {
    return new NestedWeightedPAutomatons<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W>() {

      @Override
      public void putSummaryAutomaton(
          INode<Node<ControlFlowGraph.Edge, Val>> target,
          WeightedPAutomaton<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> aut) {
        summaries.putSummaryAutomaton(target, aut);
      }

      @Override
      public WeightedPAutomaton<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W>
          getSummaryAutomaton(INode<Node<ControlFlowGraph.Edge, Val>> target) {
        if (target.fact().equals(sourceQuery.asNode())) {
          return queryToSolvers.getOrCreate(sourceQuery).getFieldAutomaton();
        }
        return summaries.getSummaryAutomaton(target);
      }
    };
  }

  public boolean preventCallRuleAdd(
      ForwardQuery sourceQuery, Rule<ControlFlowGraph.Edge, INode<Val>, W> rule) {
    return false;
  }

  protected FieldWritePOI createArrayFieldStore(Edge s) {
    Pair<Val, Integer> base = s.getStart().getArrayBase();
    return fieldWrites.getOrCreate(
        new FieldWritePOI(s, base.getX(), Field.array(base.getY()), s.getStart().getRightOp()));
  }

  protected FieldWritePOI createFieldStore(Edge cfgEdge) {
    Statement s = cfgEdge.getStart();
    Val base = s.getFieldStore().getX();
    Field field = s.getFieldStore().getY();
    Val stored = s.getRightOp();
    return fieldWrites.getOrCreate(new FieldWritePOI(cfgEdge, base, field, stored));
  }

  protected void forwardHandleFieldWrite(
      final Node<ControlFlowGraph.Edge, Val> node,
      final FieldWritePOI fieldWritePoi,
      final ForwardQuery sourceQuery) {
    BackwardQuery backwardQuery = BackwardQuery.make(node.stmt(), fieldWritePoi.getBaseVar());
    if (node.fact().equals(fieldWritePoi.getStoredVar())) {
      backwardSolve(backwardQuery);
      queryGraph.addEdge(sourceQuery, node, backwardQuery);
      queryToSolvers
          .get(sourceQuery)
          .registerStatementFieldTransitionListener(
              new ForwardHandleFieldWrite(sourceQuery, fieldWritePoi, node.stmt()));
    }
    if (node.fact().equals(fieldWritePoi.getBaseVar())) {
      queryToSolvers
          .getOrCreate(sourceQuery)
          .getFieldAutomaton()
          .registerListener(
              new TriggerBaseAllocationAtFieldWrite(
                  new SingleNode<>(node), fieldWritePoi, sourceQuery));
    }
  }

  public void unregisterAllListeners() {
    for (AbstractBoomerangSolver<W> solver : queryToSolvers.values()) {
      solver.unregisterAllListeners();
    }
    for (AbstractBoomerangSolver<W> solver : queryToBackwardSolvers.values()) {
      solver.unregisterAllListeners();
    }
    this.cfg.unregisterAllListeners();
    this.queryGraph.unregisterAllListeners();
    this.poiListeners.clear();
    this.activatedPoi.clear();
    this.fieldWrites.clear();
  }

  public DefaultValueMap<BackwardQuery, BackwardBoomerangSolver<W>> getBackwardSolvers() {
    return queryToBackwardSolvers;
  }

  public QueryGraph<W> getQueryGraph() {
    return queryGraph;
  }

  private final class EmptyFieldListener
      extends WPAStateListener<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> {

    private BackwardQuery key;
    private Node<ControlFlowGraph.Edge, Val> node;

    public EmptyFieldListener(BackwardQuery key, Node<ControlFlowGraph.Edge, Val> node) {
      super(new SingleNode<>(node));
      this.key = key;
      this.node = node;
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = super.hashCode();
      result = prime * result + getEnclosingInstance().hashCode();
      return result;
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) return true;
      if (!super.equals(obj)) return false;
      if (getClass() != obj.getClass()) return false;
      EmptyFieldListener other = (EmptyFieldListener) obj;
      if (!getEnclosingInstance().equals(other.getEnclosingInstance())) return false;
      return true;
    }

    @Override
    public void onOutTransitionAdded(
        Transition<Field, INode<Node<ControlFlowGraph.Edge, Val>>> t,
        W w,
        WeightedPAutomaton<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> weightedPAutomaton) {
      if (!t.getLabel().equals(Field.empty()) && !(t.getLabel() instanceof ArrayField)) return;
      Optional<AllocVal> allocNode = isAllocationNode(node.stmt(), node.fact());
      if (allocNode.isPresent()) {
        AllocVal val = allocNode.get();
        ForwardQuery forwardQuery;
        if (t.getLabel() instanceof ArrayField) {
          WeightedBoomerang.this
              .backwardSolverIns
              .getFieldAutomaton()
              .registerListener(
                  new ArrayAllocationListener(
                      ((ArrayField) t.getLabel()).getIndex(), t.getTarget(), val, key, node));
        } else {
          forwardQuery = new ForwardQuery(node.stmt(), val);
          forwardSolve(forwardQuery);
          queryGraph.addEdge(key, node, forwardQuery);
        }
      }
    }

    @Override
    public void onInTransitionAdded(
        Transition<Field, INode<Node<ControlFlowGraph.Edge, Val>>> t,
        W w,
        WeightedPAutomaton<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> weightedPAutomaton) {}

    private WeightedBoomerang getEnclosingInstance() {
      return WeightedBoomerang.this;
    }
  }

  private final class ArrayAllocationListener
      extends WPAStateListener<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> {

    private final int arrayAccessIndex;
    private AllocVal val;
    private BackwardQuery key;
    private Node<ControlFlowGraph.Edge, Val> node;

    public ArrayAllocationListener(
        int arrayAccessIndex,
        INode<Node<ControlFlowGraph.Edge, Val>> target,
        AllocVal val,
        BackwardQuery key,
        Node<ControlFlowGraph.Edge, Val> node) {
      super(target);
      this.arrayAccessIndex = arrayAccessIndex;
      this.val = val;
      this.key = key;
      this.node = node;
    }

    @Override
    public void onOutTransitionAdded(
        Transition<Field, INode<Node<ControlFlowGraph.Edge, Val>>> t,
        W w,
        WeightedPAutomaton<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> weightedPAutomaton) {
      if (t.getLabel().equals(Field.empty())) {
        ForwardQueryArray forwardQuery = new ForwardQueryArray(node.stmt(), val, arrayAccessIndex);
        forwardSolve(forwardQuery);
        queryGraph.addEdge(key, node, forwardQuery);
      }
      if (t.getLabel() instanceof ArrayField) {
        ForwardQueryMultiDimensionalArray forwardQuery =
            new ForwardQueryMultiDimensionalArray(
                node.stmt(), val, arrayAccessIndex, ((ArrayField) t.getLabel()).getIndex());
        forwardSolve(forwardQuery);
        queryGraph.addEdge(key, node, forwardQuery);
      }
    }

    @Override
    public void onInTransitionAdded(
        Transition<Field, INode<Node<ControlFlowGraph.Edge, Val>>> t,
        W w,
        WeightedPAutomaton<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> weightedPAutomaton) {}

    private WeightedBoomerang getEnclosingInstance() {
      return WeightedBoomerang.this;
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = super.hashCode();
      result = prime * result + getEnclosingInstance().hashCode();
      return result;
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) return true;
      if (!super.equals(obj)) return false;
      if (getClass() != obj.getClass()) return false;
      ArrayAllocationListener other = (ArrayAllocationListener) obj;
      if (!getEnclosingInstance().equals(other.getEnclosingInstance())) return false;
      return true;
    }
  }

  private final class ForwardHandleFieldWrite
      extends ControlFlowEdgeBasedFieldTransitionListener<W> {
    private final Query sourceQuery;
    private final AbstractPOI<Edge, Val, Field> fieldWritePoi;
    private final ControlFlowGraph.Edge stmt;

    private ForwardHandleFieldWrite(
        Query sourceQuery,
        AbstractPOI<Edge, Val, Field> fieldWritePoi,
        ControlFlowGraph.Edge statement) {
      super(statement);
      this.sourceQuery = sourceQuery;
      this.fieldWritePoi = fieldWritePoi;
      this.stmt = statement;
    }

    @Override
    public void onAddedTransition(Transition<Field, INode<Node<ControlFlowGraph.Edge, Val>>> t) {
      if (t.getStart() instanceof GeneratedState) return;
      if (t.getStart().fact().stmt().equals(stmt)) {
        fieldWritePoi.addFlowAllocation(sourceQuery);
      }
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + getOuterType().hashCode();
      result = prime * result + ((sourceQuery == null) ? 0 : sourceQuery.hashCode());
      return result;
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) return true;
      if (obj == null) return false;
      if (getClass() != obj.getClass()) return false;
      ForwardHandleFieldWrite other = (ForwardHandleFieldWrite) obj;
      if (!getOuterType().equals(other.getOuterType())) return false;
      if (sourceQuery == null) {
        if (other.sourceQuery != null) return false;
      } else if (!sourceQuery.equals(other.sourceQuery)) return false;
      return true;
    }

    private WeightedBoomerang getOuterType() {
      return WeightedBoomerang.this;
    }
  }

  private class TriggerBaseAllocationAtFieldWrite
      extends WPAStateListener<Field, INode<Node<Edge, Val>>, W> {

    private final PointOfIndirection<Edge, Val, Field> fieldWritePoi;
    private final ForwardQuery sourceQuery;

    public TriggerBaseAllocationAtFieldWrite(
        INode<Node<Edge, Val>> state,
        PointOfIndirection<Edge, Val, Field> fieldWritePoi,
        ForwardQuery sourceQuery) {
      super(state);
      this.fieldWritePoi = fieldWritePoi;
      this.sourceQuery = sourceQuery;
    }

    @Override
    public void onOutTransitionAdded(
        Transition<Field, INode<Node<Edge, Val>>> t,
        W w,
        WeightedPAutomaton<Field, INode<Node<Edge, Val>>, W> aut) {
      if (isAllocationNode(t.getTarget().fact().fact(), sourceQuery)) {
        fieldWritePoi.addBaseAllocation(sourceQuery);
      }
    }

    @Override
    public void onInTransitionAdded(
        Transition<Field, INode<Node<Edge, Val>>> t,
        W w,
        WeightedPAutomaton<Field, INode<Node<Edge, Val>>, W> aut) {}

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = super.hashCode();
      result = prime * result + getOuterType().hashCode();
      result = prime * result + ((fieldWritePoi == null) ? 0 : fieldWritePoi.hashCode());
      result = prime * result + ((sourceQuery == null) ? 0 : sourceQuery.hashCode());
      return result;
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) return true;
      if (!super.equals(obj)) return false;
      if (getClass() != obj.getClass()) return false;
      TriggerBaseAllocationAtFieldWrite other = (TriggerBaseAllocationAtFieldWrite) obj;
      if (!getOuterType().equals(other.getOuterType())) return false;
      if (fieldWritePoi == null) {
        if (other.fieldWritePoi != null) return false;
      } else if (!fieldWritePoi.equals(other.fieldWritePoi)) return false;
      if (sourceQuery == null) {
        if (other.sourceQuery != null) return false;
      } else if (!sourceQuery.equals(other.sourceQuery)) return false;
      return true;
    }

    private WeightedBoomerang getOuterType() {
      return WeightedBoomerang.this;
    }
  }

  private boolean isAllocationNode(Val fact, ForwardQuery sourceQuery) {
    /*TODO Replace by new designated type: see AbstractBoomerangSolver*/
    return fact.equals(sourceQuery.var().asUnbalanced(sourceQuery.cfgEdge()));
  }

  private ObservableICFG<Statement, Method> bwicfg() {
    if (bwicfg == null) bwicfg = new BackwardsObservableICFG(icfg());
    return bwicfg;
  }

  public ForwardBoomerangResults<W> solve(ForwardQuery query) {
    if (!options.allowMultipleQueries() && solving) {
      throw new RuntimeException(
          "One cannot re-use the same Boomerang solver for more than one query, unless option allowMultipleQueries is enabled. If allowMultipleQueries is enabled, ensure to call unregisterAllListeners() on this instance upon termination of all queries.");
    }
    solving = true;
    if (!analysisWatch.isRunning()) {
      analysisWatch.start();
    }
    boolean timedout = false;
    try {
      queryGraph.addRoot(query);
      LOGGER.trace("Starting forward analysis of: {}", query);
      forwardSolve(query);
      LOGGER.trace(
          "Query terminated in {} ({}), visited methods {}",
          analysisWatch,
          query,
          visitedMethods.size());
      LOGGER.trace("Query Graph \n{}", queryGraph.toDotString());
      icfg.computeFallback();
    } catch (BoomerangTimeoutException e) {
      timedout = true;
      LOGGER.trace(
          "Timeout ({}) of query: {}, visited methods {}",
          analysisWatch,
          query,
          visitedMethods.size());
    } catch (Throwable e) {
      LOGGER.error("Solving query crashed in {}", e);
    }
    if (!options.allowMultipleQueries()) {
      unregisterAllListeners();
    }

    if (analysisWatch.isRunning()) {
      analysisWatch.stop();
    }
    return new ForwardBoomerangResults<W>(
        query,
        icfg(),
        cfg(),
        timedout,
        this.queryToSolvers,
        getStats(),
        analysisWatch,
        visitedMethods,
        options.trackDataFlowPath(),
        options.prunePathConditions(),
        options.trackImplicitFlows());
  }

  public BackwardBoomerangResults<W> solve(BackwardQuery query) {
    return solve(query, true);
  }

  public BackwardBoomerangResults<W> solve(BackwardQuery query, boolean timing) {
    if (!options.allowMultipleQueries() && solving) {
      throw new RuntimeException(
          "One cannot re-use the same Boomerang solver for more than one query, unless option allowMultipleQueries is enabled. If allowMultipleQueries is enabled, ensure to call unregisterAllListeners() on this instance upon termination of all queries.");
    }
    solving = true;
    if (timing && !analysisWatch.isRunning()) {
      analysisWatch.start();
    }
    boolean timedout = false;
    try {
      queryGraph.addRoot(query);
      LOGGER.trace("Starting backward analysis of: {}", query);
      backwardSolve(query);
    } catch (BoomerangTimeoutException e) {
      timedout = true;
      LOGGER.trace("Timeout ({}) of query: {} ", analysisWatch, query);
    }
    debugOutput();
    // printAllBackwardCallAutomatonFlow();
    if (!options.allowMultipleQueries()) {
      unregisterAllListeners();
    }
    if (timing && analysisWatch.isRunning()) {
      analysisWatch.stop();
    }
    return new BackwardBoomerangResults<W>(
        query, timedout, this.queryToSolvers, backwardSolverIns, getStats(), analysisWatch);
  }

  public BackwardBoomerangResults<W> solveUnderScope(
      BackwardQuery query, Node<Edge, Val> triggeringNode, Query parentQuery) {
    if (!options.allowMultipleQueries() && solving) {
      throw new RuntimeException(
          "One cannot re-use the same Boomerang solver for more than one query, unless option allowMultipleQueries is enabled. If allowMultipleQueries is enabled, ensure to call unregisterAllListeners() on this instance upon termination of all queries.");
    }
    solving = true;
    if (!analysisWatch.isRunning()) {
      analysisWatch.start();
    }
    boolean timedout = false;
    try {

      LOGGER.trace("Starting backward analysis of: {}", query);
      backwardSolve(query);
      queryGraph.addEdge(parentQuery, triggeringNode, query);
      this.debugOutput();
    } catch (BoomerangTimeoutException e) {
      timedout = true;
      LOGGER.trace("Timeout ({}) of query: {} ", analysisWatch, query);
    }
    if (analysisWatch.isRunning()) {
      analysisWatch.stop();
    }
    return new BackwardBoomerangResults<W>(
        query, timedout, this.queryToSolvers, backwardSolverIns, getStats(), analysisWatch);
  }

  public ForwardBoomerangResults<W> solveUnderScope(
      ForwardQuery query, Node<Edge, Val> triggeringNode, Query parentQuery) {
    if (!options.allowMultipleQueries() && solving) {
      throw new RuntimeException(
          "One cannot re-use the same Boomerang solver for more than one query, unless option allowMultipleQueries is enabled. If allowMultipleQueries is enabled, ensure to call unregisterAllListeners() on this instance upon termination of all queries.");
    }
    solving = true;
    if (!analysisWatch.isRunning()) {
      analysisWatch.start();
    }
    boolean timedout = false;
    try {
      LOGGER.trace("Starting forward analysis of: {}", query);
      forwardSolve(query);
      queryGraph.addEdge(parentQuery, triggeringNode, query);
      LOGGER.trace(
          "Query terminated in {} ({}), visited methods {}",
          analysisWatch,
          query,
          visitedMethods.size());
    } catch (BoomerangTimeoutException e) {
      timedout = true;
      LOGGER.trace(
          "Timeout ({}) of query: {}, visited methods {}",
          analysisWatch,
          query,
          visitedMethods.size());
    } catch (Throwable e) {
      LOGGER.error("Solving query crashed in {}", e);
    }
    if (!options.allowMultipleQueries()) {
      unregisterAllListeners();
    }

    if (analysisWatch.isRunning()) {
      analysisWatch.stop();
    }
    return new ForwardBoomerangResults<W>(
        query,
        icfg(),
        cfg(),
        timedout,
        this.queryToSolvers,
        getStats(),
        analysisWatch,
        visitedMethods,
        options.trackDataFlowPath(),
        options.prunePathConditions(),
        options.trackImplicitFlows());
  }

  public void debugOutput() {
    if (LOGGER.isTraceEnabled()) {
      LOGGER.trace("Query Graph \n{}", queryGraph.toDotString());
      // LOGGER.trace("Terminated backward analysis of: {}", query);
      LOGGER.trace("#ForwardSolvers: {}", queryToSolvers.size());
      printAllAutomata();
      printAllForwardCallAutomatonFlow();
      printAllBackwardCallAutomatonFlow();
    }
  }

  protected void backwardSolve(BackwardQuery query) {
    if (!options.aliasing()) return;
    AbstractBoomerangSolver<W> solver = queryToBackwardSolvers.getOrCreate(query);
    INode<Node<ControlFlowGraph.Edge, Val>> fieldTarget = solver.createQueryNodeField(query);
    INode<Val> callTarget =
        solver.generateCallState(new SingleNode<>(query.var()), query.cfgEdge());
    if (rootQuery == null) {
      rootQuery = callTarget;
    }
    solver.solve(query.asNode(), Field.empty(), fieldTarget, query.cfgEdge(), callTarget);
  }

  private AbstractBoomerangSolver<W> forwardSolve(ForwardQuery query) {
    ControlFlowGraph.Edge cfgEdge = query.asNode().stmt();
    AbstractBoomerangSolver<W> solver = queryToSolvers.getOrCreate(query);
    INode<Node<ControlFlowGraph.Edge, Val>> fieldTarget = solver.createQueryNodeField(query);
    INode<Val> callTarget =
        solver.generateCallState(new SingleNode<>(query.var()), query.cfgEdge());
    Statement stmt = cfgEdge.getStart();
    if (!(stmt.isFieldStore())
        && query instanceof ForwardQueryArray
        && options.getArrayStrategy() != ArrayStrategy.DISABLED) {
      if (query instanceof ForwardQueryMultiDimensionalArray) {
        ForwardQueryMultiDimensionalArray arrayQuery = ((ForwardQueryMultiDimensionalArray) query);
        Node<ControlFlowGraph.Edge, Val> node =
            new Node<>(query.cfgEdge(), ((AllocVal) query.var()).getDelegate());
        SingleNode<Node<ControlFlowGraph.Edge, Val>> sourveVal = new SingleNode<>(node);
        INode<Node<ControlFlowGraph.Edge, Val>> genState1 =
            solver.generateFieldState(sourveVal, Field.array(arrayQuery.getIndex1()));
        insertTransition(
            solver.getFieldAutomaton(),
            new Transition<>(sourveVal, Field.array(arrayQuery.getIndex1()), genState1));
        INode<Node<ControlFlowGraph.Edge, Val>> genState2 =
            solver.generateFieldState(sourveVal, Field.array(arrayQuery.getIndex2()));
        insertTransition(
            solver.getFieldAutomaton(),
            new Transition<>(genState1, Field.array(arrayQuery.getIndex2()), genState2));
        insertTransition(
            solver.getFieldAutomaton(), new Transition<>(genState2, Field.empty(), fieldTarget));
      } else {
        ForwardQueryArray arrayQuery = ((ForwardQueryArray) query);
        Node<ControlFlowGraph.Edge, Val> node =
            new Node<>(query.cfgEdge(), ((AllocVal) query.var()).getDelegate());
        SingleNode<Node<ControlFlowGraph.Edge, Val>> sourceVal = new SingleNode<>(node);
        INode<Node<ControlFlowGraph.Edge, Val>> genState =
            solver.generateFieldState(sourceVal, Field.array(arrayQuery.getIndex()));
        insertTransition(
            solver.getFieldAutomaton(),
            new Transition<>(sourceVal, Field.array(arrayQuery.getIndex()), genState));
        insertTransition(
            solver.getFieldAutomaton(), new Transition<>(genState, Field.empty(), fieldTarget));
      }
    }
    if (stmt.isStringAllocation()) {
      // Scene.v().forceResolve("java.lang.String",
      // SootClass.BODIES);
      //        	throw new RuntimeException("Not properly implemented String allocation site");
      //            SootClass stringClass = Scene.v().getSootClass("java.lang.String");
      //            if (stringClass.declaresField("char[] value")) {
      //                SootField valueField = stringClass.getField("char[] value");
      //                SingleNode<Node<Statement, Val>> s = new SingleNode<Node<Statement,
      // Val>>(query.asNode());
      //                INode<Node<Statement, Val>> irState =
      // solver.getFieldAutomaton().createState(s,
      //                        new Field(valueField));
      //                insertTransition(solver.getFieldAutomaton(), new Transition<Field,
      // INode<Node<Statement, Val>>>(
      //                        new SingleNode<Node<Statement, Val>>(query.asNode()), new
      // Field(valueField), irState));
      //                insertTransition(solver.getFieldAutomaton(), new Transition<Field,
      // INode<Node<Statement, Val>>>(
      //                        irState, Field.empty(),
      // solver.getFieldAutomaton().getInitialState()));
      //            }
    }
    Val var;
    Field field;
    if (stmt.isFieldStore()) {
      field = stmt.getFieldStore().getY();
      var = stmt.getFieldStore().getX();
      forwardHandleFieldWrite(
          new Node<>(cfgEdge, stmt.getRightOp()),
          new FieldWritePOI(cfgEdge, var, field, stmt.getRightOp()),
          query);
    } else {
      var = query.var();
      if (var instanceof AllocVal) {
        var = ((AllocVal) var).getDelegate();
      }

      field = Field.empty();
    }
    if (query instanceof WeightedForwardQuery) {
      WeightedForwardQuery<W> q = (WeightedForwardQuery<W>) query;
      // Convert AllocVal -> Val
      solver.solve(new Node<>(cfgEdge, var), field, fieldTarget, cfgEdge, callTarget, q.weight());
    } else {
      // Convert AllocVal -> Val
      solver.solve(new Node<>(cfgEdge, var), field, fieldTarget, cfgEdge, callTarget);
    }

    return solver;
  }

  private boolean insertTransition(
      final WeightedPAutomaton<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> aut,
      Transition<Field, INode<Node<ControlFlowGraph.Edge, Val>>> transition) {
    if (!aut.nested()) {
      return aut.addTransition(transition);
    }
    INode<Node<ControlFlowGraph.Edge, Val>> target = transition.getTarget();
    if (!(target instanceof GeneratedState)) {
      forwardFieldSummaries.putSummaryAutomaton(target, aut);

      aut.registerListener(
          (t, w, aut12) -> {
            if (t.getStart() instanceof GeneratedState) {
              WeightedPAutomaton<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> n =
                  forwardFieldSummaries.getSummaryAutomaton(t.getStart());
              aut12.addNestedAutomaton(n);
            }
          });
      return aut.addTransition(transition);
    }
    final WeightedPAutomaton<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> nested =
        forwardFieldSummaries.getSummaryAutomaton(target);
    nested.registerListener(
        (t, w, aut1) -> {
          if (t.getStart() instanceof GeneratedState) {
            WeightedPAutomaton<Field, INode<Node<ControlFlowGraph.Edge, Val>>, W> n =
                forwardFieldSummaries.getSummaryAutomaton(t.getStart());
            aut1.addNestedAutomaton(n);
          }
        });
    return nested.addTransition(transition);
  }

  public class FieldWritePOI extends AbstractPOI<Edge, Val, Field> {

    public FieldWritePOI(Edge statement, Val base, Field field, Val stored) {
      super(statement, base, field, stored);
    }

    @Override
    public void execute(final ForwardQuery baseAllocation, final Query flowAllocation) {
      if (flowAllocation instanceof BackwardQuery) {
      } else if (flowAllocation instanceof ForwardQuery) {
        ForwardBoomerangSolver<W> baseSolver = queryToSolvers.get(baseAllocation);
        ForwardBoomerangSolver<W> flowSolver = queryToSolvers.get(flowAllocation);
        ExecuteImportFieldStmtPOI<W> exec =
            new ExecuteImportFieldStmtPOI<W>(baseSolver, flowSolver, FieldWritePOI.this) {
              public void activate(INode<Node<Edge, Val>> start) {
                activateAllPois(new SolverPair(flowSolver, baseSolver), start);
              };
            };
        registerActivationListener(new SolverPair(flowSolver, baseSolver), exec);
        exec.solve();
      }
    }
  }

  protected void activateAllPois(SolverPair pair, INode<Node<Edge, Val>> start) {
    if (activatedPoi.put(pair, start)) {
      Collection<ExecuteImportFieldStmtPOI<W>> listeners = poiListeners.get(pair);
      for (ExecuteImportFieldStmtPOI<W> l : Lists.newArrayList(listeners)) {
        l.trigger(start);
      }
    }
  }

  public void registerActivationListener(SolverPair solverPair, ExecuteImportFieldStmtPOI<W> exec) {
    Collection<INode<Node<Edge, Val>>> listeners = activatedPoi.get(solverPair);
    for (INode<Node<Edge, Val>> node : Lists.newArrayList(listeners)) {
      exec.trigger(node);
    }
    poiListeners.put(solverPair, exec);
  }

  private class SolverPair {

    private AbstractBoomerangSolver<W> flowSolver;
    private AbstractBoomerangSolver<W> baseSolver;

    public SolverPair(
        AbstractBoomerangSolver<W> flowSolver, AbstractBoomerangSolver<W> baseSolver) {
      this.flowSolver = flowSolver;
      this.baseSolver = baseSolver;
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + getOuterType().hashCode();
      result = prime * result + ((baseSolver == null) ? 0 : baseSolver.hashCode());
      result = prime * result + ((flowSolver == null) ? 0 : flowSolver.hashCode());
      return result;
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) return true;
      if (obj == null) return false;
      if (getClass() != obj.getClass()) return false;
      SolverPair other = (SolverPair) obj;
      if (!getOuterType().equals(other.getOuterType())) return false;
      if (baseSolver == null) {
        if (other.baseSolver != null) return false;
      } else if (!baseSolver.equals(other.baseSolver)) return false;
      if (flowSolver == null) {
        if (other.flowSolver != null) return false;
      } else if (!flowSolver.equals(other.flowSolver)) return false;
      return true;
    }

    private WeightedBoomerang getOuterType() {
      return WeightedBoomerang.this;
    }
  }

  public ObservableICFG<Statement, Method> icfg() {
    return icfg;
  }

  public ObservableControlFlowGraph cfg() {
    return cfg;
  }

  protected abstract WeightFunctions<ControlFlowGraph.Edge, Val, Field, W> getForwardFieldWeights();

  protected abstract WeightFunctions<ControlFlowGraph.Edge, Val, Field, W>
      getBackwardFieldWeights();

  protected abstract WeightFunctions<ControlFlowGraph.Edge, Val, ControlFlowGraph.Edge, W>
      getBackwardCallWeights();

  protected abstract WeightFunctions<ControlFlowGraph.Edge, Val, ControlFlowGraph.Edge, W>
      getForwardCallWeights(ForwardQuery sourceQuery);

  public DefaultValueMap<ForwardQuery, ForwardBoomerangSolver<W>> getSolvers() {
    return queryToSolvers;
  }

  public void debugOutput(Debugger<W> debugger) {
    debugger.done(icfg, cfg, visitedMethods, queryToSolvers);
  }

  public IBoomerangStats<W> getStats() {
    return stats;
  }

  public void onCreateSubSolver(Query key, AbstractBoomerangSolver<W> solver) {
    for (SolverCreationListener<W> l : solverCreationListeners) {
      l.onCreatedSolver(key, solver);
    }
  }

  public void registerSolverCreationListener(SolverCreationListener<W> l) {
    if (solverCreationListeners.add(l)) {
      for (Entry<ForwardQuery, ForwardBoomerangSolver<W>> e :
          Lists.newArrayList(queryToSolvers.entrySet())) {
        l.onCreatedSolver(e.getKey(), e.getValue());
      }
    }
  }

  public Table<ControlFlowGraph.Edge, Val, W> getResults(ForwardQuery seed) {
    final Table<ControlFlowGraph.Edge, Val, W> results = HashBasedTable.create();
    WeightedPAutomaton<ControlFlowGraph.Edge, INode<Val>, W> fieldAut =
        queryToSolvers.getOrCreate(seed).getCallAutomaton();
    for (Entry<Transition<ControlFlowGraph.Edge, INode<Val>>, W> e :
        fieldAut.getTransitionsToFinalWeights().entrySet()) {
      Transition<ControlFlowGraph.Edge, INode<Val>> t = e.getKey();
      W w = e.getValue();
      if (t.getLabel().equals(Statement.epsilon())) continue;
      if (t.getStart().fact().isLocal()
          && !t.getLabel().getStart().getMethod().equals(t.getStart().fact().m())) continue;
      results.put(t.getLabel(), t.getStart().fact(), w);
    }
    return results;
  }

  public BoomerangOptions getOptions() {
    return this.options;
  }

  public CallGraph getCallGraph() {
    return this.callGraph;
  }

  public Set<Method> getVisitedMethods() {
    return visitedMethods;
  }

  // For debugging purpose

  public void printCallAutomatonFlow(AbstractBoomerangSolver<W> solver) {
    final Table<ControlFlowGraph.Edge, Val, W> results = HashBasedTable.create();
    WeightedPAutomaton<ControlFlowGraph.Edge, INode<Val>, W> callAut = solver.getCallAutomaton();
    for (Entry<Transition<ControlFlowGraph.Edge, INode<Val>>, W> e :
        callAut.getTransitionsToFinalWeights().entrySet()) {
      Transition<ControlFlowGraph.Edge, INode<Val>> t = e.getKey();
      W w = e.getValue();
      if (t.getLabel().getStart().equals(Statement.epsilon())) continue;
      if (t.getStart().fact().isLocal()
          && !t.getLabel().getStart().getMethod().equals(t.getStart().fact().m())) continue;
      results.put(t.getLabel(), t.getStart().fact(), w);
    }
    LOGGER.trace("Call Automaton flow for {}", solver);
    printResultsPerMethod(results);
  }

  private void printResultsPerMethod(Table<ControlFlowGraph.Edge, Val, W> results) {
    Multimap<Method, Cell<ControlFlowGraph.Edge, Val, W>> methodToRes = HashMultimap.create();
    for (Cell<ControlFlowGraph.Edge, Val, W> c : results.cellSet()) {
      methodToRes.put(c.getRowKey().getStart().getMethod(), c);
    }

    for (Method m : methodToRes.keySet()) {
      LOGGER.trace("Results in Method {}: ", m);
      for (Statement s : m.getStatements()) {
        LOGGER.trace("\tStatement {}: ", s);
        for (Cell<ControlFlowGraph.Edge, Val, W> c : methodToRes.get(m)) {
          if (c.getRowKey().getStart().equals(s)) {
            LOGGER.trace("\t\tVal: {}, W: {}", c.getColumnKey(), c.getValue() + " ");
          }
        }
      }
    }
  }

  public void printAllForwardCallAutomatonFlow() {
    for (Entry<ForwardQuery, ForwardBoomerangSolver<W>> e : queryToSolvers.entrySet()) {
      printCallAutomatonFlow(e.getValue());
    }
  }

  public void printAllBackwardCallAutomatonFlow() {
    for (Entry<BackwardQuery, BackwardBoomerangSolver<W>> e : queryToBackwardSolvers.entrySet()) {
      printCallAutomatonFlow(e.getValue());
    }
  }

  public void printAllAutomata() {
    for (Entry<ForwardQuery, ForwardBoomerangSolver<W>> e : queryToSolvers.entrySet()) {
      printAutomata(e.getKey());
    }

    LOGGER.trace("Backward Solver");

    for (Entry<BackwardQuery, BackwardBoomerangSolver<W>> e : queryToBackwardSolvers.entrySet()) {
      printAutomata(e.getKey());
    }
  }

  public void printAutomata(Query q) {
    if (LOGGER.isTraceEnabled() && q instanceof ForwardQuery) {
      LOGGER.trace("Solver {}", queryToSolvers.get(q).getQuery());
      LOGGER.trace("Field Automaton\n {}", queryToSolvers.get(q).getFieldAutomaton().toDotString());
      LOGGER.trace("Call Automaton\n {}", queryToSolvers.get(q).getCallAutomaton().toDotString());
    }
    if (LOGGER.isTraceEnabled() && q instanceof BackwardQuery) {
      LOGGER.trace("Solver {}", queryToBackwardSolvers.get(q));
      LOGGER.trace(
          "Field Automaton\n {}", queryToBackwardSolvers.get(q).getFieldAutomaton().toDotString());
      LOGGER.trace(
          "Call Automaton\n {}", queryToBackwardSolvers.get(q).getCallAutomaton().toDotString());
    }
  }

  private void printStats() {
    int forwardCallTransitions = 0;
    int backwardCallTransitions = 0;
    int forwardFieldTransitions = 0;
    int backwardFieldTransitions = 0;
    for (Entry<ForwardQuery, ForwardBoomerangSolver<W>> e : queryToSolvers.entrySet()) {
      if (e.getKey() instanceof ForwardQuery) {
        forwardCallTransitions += e.getValue().getCallAutomaton().getTransitions().size();
        forwardFieldTransitions += e.getValue().getFieldAutomaton().getTransitions().size();
      } else {
        backwardCallTransitions += e.getValue().getCallAutomaton().getTransitions().size();
        backwardFieldTransitions += e.getValue().getFieldAutomaton().getTransitions().size();
      }
    }
    LOGGER.trace("Forward Call Transitions: {}", forwardCallTransitions);
    LOGGER.trace("Forward Field Transitions: {}", forwardFieldTransitions);

    LOGGER.trace("Backward Call Transitions: {}", backwardCallTransitions);
    LOGGER.trace("Backward Field Transitions: {}", backwardFieldTransitions);
  }

  private void printQueryTimes() {
    for (Entry<ForwardQuery, ForwardBoomerangSolver<W>> entry : queryToSolvers.entrySet()) {
      LOGGER.trace("{}", entry.getKey());
      LOGGER.trace("Call Automaton Time: {}", entry.getValue().getCallAutomaton().getWatch());
      LOGGER.trace("Field Automaton Time: {}", entry.getValue().getFieldAutomaton().getWatch());
    }
  }

  private void printElapsedTimes() {
    // LOGGER.debug("BackwardCallWatch " + backwardSolver.getCallAutomaton().getWatch());
    // LOGGER.debug("BackwardFieldWatch " + backwardSolver.getFieldAutomaton().getWatch());
    long forwardCallElaps = 0;
    long forwardFieldElaps = 0;
    for (ForwardBoomerangSolver<W> v : queryToSolvers.values()) {
      forwardCallElaps += v.getCallAutomaton().getWatch().elapsed(TimeUnit.SECONDS);
      forwardFieldElaps += v.getFieldAutomaton().getWatch().elapsed(TimeUnit.SECONDS);
    }

    LOGGER.trace("ForwardCallWatch " + forwardCallElaps + " s");
    LOGGER.trace("ForwardFieldWatch " + forwardFieldElaps + " s");
  }

  private void printRules() {
    // LOGGER.debug("BackwardCallRules " + backwardSolver.getCallPDS().getAllRules().size());
    // LOGGER.debug("BackwardFieldRules " + backwardSolver.getFieldPDS().getAllRules().size());
    long forwardCallElaps = 0;
    long forwardFieldElaps = 0;
    Set<Rule> allCallRules = Sets.newHashSet();
    Set<Rule> allFieldRules = Sets.newHashSet();
    for (ForwardBoomerangSolver<W> v : queryToSolvers.values()) {
      allCallRules.addAll(v.getCallPDS().getAllRules());
      allFieldRules.addAll(v.getFieldPDS().getAllRules());
      forwardCallElaps += v.getCallPDS().getAllRules().size();
      forwardFieldElaps += v.getFieldPDS().getAllRules().size();
    }

    LOGGER.trace("ForwardCallRules (total)" + forwardCallElaps);
    LOGGER.trace("ForwardFieldRules (total)" + forwardFieldElaps);

    LOGGER.trace("ForwardCallRules (deduplicated)" + allCallRules.size());
    LOGGER.trace("ForwardFieldRules (deduplicated)" + allFieldRules.size());
  }
}
