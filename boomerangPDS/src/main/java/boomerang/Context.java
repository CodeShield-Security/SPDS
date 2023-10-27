package boomerang;

import boomerang.jimple.Statement;

/**
 * A context is stored within the context graph. And must at least have a statement associated with it. 
 * 
 * @author "Johannes Spaeth"
 *
 */
public interface Context {
    public Statement getStmt();

    public int hashCode();

    public boolean equals(Object obj);
}