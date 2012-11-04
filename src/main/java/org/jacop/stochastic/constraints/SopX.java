package org.jacop.stochastic.constraints;

import java.util.ArrayList;
import java.util.HashMap;

import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.stochastic.core.Operator;
import org.jacop.stochastic.core.Operator.CompOp;
import org.jacop.stochastic.core.ProbabilityRange;
import org.jacop.stochastic.core.StochasticDomain;
import org.jacop.stochastic.core.StochasticVar;

/**
 * Implements the SopX constraint according to a reification probability factor
 * where S is a StochasticVar and X is an IntVar. The operation op can be 
 * "<", "<=", "==", ">" or ">=".
 */
public class SopX extends Constraint {

    static int IdNumber = 1;

    /**
     * StochasticVar to be compared.
     */
    public StochasticVar S;
	
    /**
     * IntVar to be compared.
     */
    public IntVar X;
	
    /**
     * Reification probaility factor.
     */
    public StochasticVar P;
		
    /**
     * Desired operation between S and X -
     * "LESS", "LESS_EQUAL", "EQUAL", "GREATER" or "GREATER_EQUAL"
     */
    public Operator op;
	
    /**
     * Mapping of operation satisfying links between S and X.
     */
    private HashMap<Integer, ArrayList<Integer>> l2r;
	
    /**
     * Mapping of operation satisfying links between S and X for the 
     * current invocation of consistency.
     */
    private HashMap<Integer, ArrayList<Integer>> l2rCurrent;
	
    /**
     * This constructor creates a new SopX constraint.
     * @param S : StochasticVar to be compared.
     * @param X : IntVar to be compared.
     * @param P : Reification probaility factor, modelled as an IntVar.
     * @param op : Desired operation between S and X.
     */
    public SopX(StochasticVar S, IntVar X, StochasticVar P, Operator op){
		
	assert (op.cOp != CompOp.INVALID): "Invalid Operation";	
		
	this.queueIndex = 1;
	this.numberId = IdNumber++;
	this.numberArgs = (short)(3);
	this.S = S;
	this.X = X;
	this.P = P;
	this.op = op;
		
	computeMappings();
    }
	
    /**
     * This method computes l2r attribute of the constraint.
     */
    private void computeMappings() {
		
	l2r = new HashMap<Integer, ArrayList<Integer>>(S.getSize());
		
	for (int i : S.dom().values){
			
	    ArrayList<Integer> map = new ArrayList<Integer>(0);
				
            for (ValueEnumeration e = X.dom().valueEnumeration(); e.hasMoreElements();) {
                int j = e.nextElement();
		if (op.doCompOp(i, j))
		    map.add(j);
            }

	    l2r.put(i, map);
	}

	// System.out.println(l2r);
    }
	
    @Override
	public ArrayList<Var> arguments() {
		
	ArrayList<Var> variables = new ArrayList<Var>(3);
	variables.add(S);
	variables.add(X);
	variables.add(P);
		
	return variables;
    }

    @Override
	public void consistency(Store store) {
		
	do{
	    store.propagationHasOccurred = false;
		
	    IntDomain XdomCopy = X.dom().cloneLight();
	    ProbabilityRange R = new ProbabilityRange(1,0);
						
	    for (int i=0; i < XdomCopy.getSize(); i++) {
			
		ProbabilityRange r = new ProbabilityRange(0);

		// TODO, RADEK
		// BAD, OO programming, it should not change global attribute l2rCurrent 
		// since it is used only here. ( satisfied does not count). 
		// It could remain like this if it was used across different consistency executions
		// keep removing until backtrack has occurred during which restart from the original takes place.
				
		boolean remove = true;
		removeDeadLinks(XdomCopy.getElementAt(i));
								
		for (int j=0; j < S.getSize(); j++) {
					
		    ArrayList<Integer> map = l2rCurrent.get(new Integer(S.dom().values[j]));
					
		    if (map.size() > 0) {
						
			remove = false;
			for (int k = 0; k < map.size(); k++){
			    // wrong to remove from S, as commented below, since probability P can be sum of several 
			    // probabilities, if we use other relations as "==" as an operator.
			    //S.dom().inElement(store.level, S, S.dom().values[j], P.dom().ProbRanges[0]);
			    r.add(S.dom().ProbRanges[j]);
			}
		    }
		}
				
		R.union(r);
				
		if (remove == true && P.dom().ProbRanges[0].min != 0)
		    X.dom().inComplement(store.level, X, XdomCopy.getElementAt(i));
	    }
			
	    P.dom().inElement(store.level, P, P.dom().values[0], R);

	} while(store.propagationHasOccurred);
    }

    private void removeDeadLinks(int Xval) {
		
	//TODO, Radek, why not just have a separate hashmap for each value of X (in case of X being very small domain). 
	// or at least compute it from scratch if X is large as mapOrig can have huge number of arrays? e.g. what happens if X has domain 1..100000?
	l2rCurrent = new HashMap<Integer, ArrayList<Integer>>(S.getSize());

	for (int i : S.dom().values){
			
	    ArrayList<Integer> mapOrig = l2r.get(i);
	    ArrayList<Integer> mapCurr = new ArrayList<Integer>();
			
	    for (int j = 0; j < mapOrig.size(); j++)
		if (mapOrig.get(j).equals(Xval))
		    mapCurr.add(mapOrig.get(j));
			
	    l2rCurrent.put(i, mapCurr);
	}
    }
	
    @Override
	public int getConsistencyPruningEvent(Var var) {
		
	// If consistency function mode
	if (consistencyPruningEvents != null) {
	    Integer possibleEvent = consistencyPruningEvents.get(var);
	    if (possibleEvent != null)
		return possibleEvent;
	}
	return StochasticDomain.BOUND;
    }

    @Override
	public String id() {
		
	if (id != null)
	    return id;
	else
	    return this.getClass().getSimpleName() + numberId;
    }

    @Override
	public void impose(Store store) {
		
	S.putModelConstraint(this, getConsistencyPruningEvent(S));
	X.putModelConstraint(this, getConsistencyPruningEvent(X));
	P.putModelConstraint(this, getConsistencyPruningEvent(P));

	store.addChanged(this);
	store.countConstraint();	
    }

    @Override
	public void removeConstraint() {

	S.removeConstraint(this);
	X.removeConstraint(this);
	P.removeConstraint(this);
    }

    @Override
	public boolean satisfied() {
		
	IntDomain XdomCopy = X.dom().cloneLight();
	ProbabilityRange R = new ProbabilityRange(1,0);
					
	for (int i=0; i < XdomCopy.getSize(); i++) {
		
	    ProbabilityRange r = new ProbabilityRange(0);

	    removeDeadLinks(XdomCopy.getElementAt(i));
							
	    for (int j=0; j < S.getSize(); j++) {
				
		ArrayList<Integer> map = l2rCurrent.get(new Integer(S.dom().values[j]));
				
		if (map.size() > 0){
					
		    for (int k = 0; k < map.size(); k++){
			r.add(S.dom().ProbRanges[j]);
		    }
		}
	    }
			
	    R.union(r);
			
	}
		
	if (!P.dom().ProbRanges[0].eq(R))
	    return false;

	return true;
    }

    @Override
	public String toString() {
		
	StringBuffer result = new StringBuffer( id() );
		
	result.append(" : SopX( " + S + " " + op.cOp + " " + X
		      + "<=>" + P + ")");
		
	return result.toString();
    }

    @Override
	public void increaseWeight() {
		
	if (increaseWeight) {
	    S.weight++;
	    X.weight++;
	    P.weight++;
	}	
    }

}
