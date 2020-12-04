package boomerang.staticfields;

import boomerang.scene.ControlFlowGraph.Edge;
import boomerang.scene.Field;
import boomerang.scene.Statement;
import boomerang.scene.StaticFieldVal;
import boomerang.scene.Val;
import com.google.common.collect.Multimap;
import java.util.Set;
import wpds.impl.Weight;
import wpds.interfaces.State;

public class SingletonStaticFieldStrategy<W extends Weight> implements StaticFieldStrategy<W> {

  private Multimap<Field, Statement> fieldStoreStatements;
  private Multimap<Field, Statement> fieldLoadStatements;

  public SingletonStaticFieldStrategy() {
    // this.fieldStoreStatements = boomerang.getCallGraph().getFieldStoreStatements();
    // this.fieldLoadStatements = boomerang.getCallGraph().getFieldLoadStatements();
  }

  @Override
  public void handleForward(
      Edge storeStmt, Val storedVal, StaticFieldVal staticVal, Set<State> out) {
    // TODO Fix logic
    /*  for (Statement matchingStore : fieldLoadStatements.get(staticVal.field())) {
      for (Statement succ :
          matchingStore.getMethod().getControlFlowGraph().getSuccsOf(matchingStore)) {

        solver.processNormal(
            new Node<>(storeStmt, storedVal),
            new Node<>(new Edge(matchingStore, succ), matchingStore.getLeftOp()));
      }
    }*/
  }

  @Override
  public void handleBackward(
      Edge loadStatement, Val loadedVal, StaticFieldVal staticVal, Set<State> out) {
    // TODO Fix logic
    /* for (Statement matchingStore : fieldStoreStatements.get(staticVal.field())) {
      for (Statement pred :
          matchingStore.getMethod().getControlFlowGraph().getPredsOf(matchingStore)) {
          solver.processNormal(
        new Node<>(loadStatement, loadedVal),
        new Node<>(new Edge(pred, matchingStore), matchingStore.getRightOp()));
      }
    }*/
  }
}
