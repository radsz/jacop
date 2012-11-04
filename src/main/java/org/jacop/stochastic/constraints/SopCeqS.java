package org.jacop.stochastic.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.stochastic.core.Link;
import org.jacop.stochastic.core.Operator;
import org.jacop.stochastic.core.Operator.ArithOp;
import org.jacop.stochastic.core.ProbabilityRange;
import org.jacop.stochastic.core.StochasticDomain;
import org.jacop.stochastic.core.StochasticVar;

/**
 * Implements the constraint Slhs op C = Srhs where Slhs and Srhs are 
 * StochasticVars and C is a constant. 
 * The operation op can be "+", "-", "*" or "/" .
 */
public class SopCeqS extends Constraint{

	// TODO, Radek, This constraint assumes 1 to 1 correspondencace between values of left and right stochastic var. 
	// this is not right for constraint like Smul0eqS as many elements become zero, of course this is rather stupid
	// constraint to have but it should protect against it. 
    // What is more important since there is one to one correpondence between values why not use 
	// directly object Link instead of ArrayList, e.g. HashMap<Integer, Link> l2r;
	// Link could also contain the position of the value not just leaf value (or even instead of ) so no search is needed.
	static int IdNumber = 1;

	/**
	 * StochasticVar on the left hand side.
	 */
	public StochasticVar Slhs;
	
	/**
	 * StochasticVar on the right hand side.
	 */
	public StochasticVar Srhs;
	
	/**
	 * Specified constant.
	 */
	public int C;
		
	/**
	 * Desired operation : "+", "-", "*" or "/".
	 */
	public Operator op;

	/**
	 * Mapping of Slhs values to Srhs values.
	 */
	private HashMap<Integer, ArrayList<Link>> l2r;
	
	/**
	 * Mapping of Srhs values to Slhs values.
	 */
	private HashMap<Integer, ArrayList<Link>> r2l;
		
	/**
	 * This constructor creates a new SopCeqS constraint.
	 * @param Slhs : StochasticVar on the left hand side
	 * @param op : Desired operation
	 * @param C : Specified constant
	 * @param Srhs : StochasticVar on the right hand side
	 */
	public SopCeqS(StochasticVar Slhs, Operator op, int C, StochasticVar Srhs){
		
		assert (op.aOp != ArithOp.INVALID): "Invalid Operation";
		
		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.numberArgs = (short)(2) ;
		this.Slhs = Slhs;
		this.op = op;
		this.C = C;
		this.Srhs = Srhs;	
		
		computeMappings();
	}
	
	/**
	 * Computes the mappings between the values of Slhs and Srhs in both
	 * directions.
	 */
	private void computeMappings() {

		l2r = new HashMap<Integer, ArrayList<Link>>(Slhs.getSize());
		
		for (int i : Slhs.dom().values){
			
			ArrayList<Link> map = new ArrayList<Link>(0);
			
			for (int j : Srhs.dom().values){
				
				if (op.doArithOp(i, C) == j ){
					map.add(new Link(C, j));
				}
			}
			l2r.put(i, map);
		}
		
		r2l = new HashMap<Integer, ArrayList<Link>>(Slhs.getSize());

		for (int i : Srhs.dom().values){
			
			ArrayList<Link> map = new ArrayList<Link>(0);
			
			for (int j : Slhs.dom().values) {
				
				if( op.doArithOp(j, C) == i ) {
					map.add(new Link(C, j));
				}
			}
			r2l.put(i, map);
		}			
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(2);
		variables.add(Slhs);
		variables.add(Srhs);

		return variables;
	}

	@Override
	public void consistency(Store store) {

		do{
			store.propagationHasOccurred = false;
			
			for (int i : Slhs.dom().values){
				
				ArrayList<Link> map = l2r.get(new Integer(i));
				
				if (map.size() > 0){
					
					assert (map.size() == 1);
					int index = Arrays.binarySearch(Srhs.dom().values, map.get(0).leaf);
					Slhs.dom().inElement(store.level, Slhs, i, Srhs.dom().ProbRanges[index]);
				}
				else
					Slhs.dom().inElement(store.level, Slhs, i, new ProbabilityRange(0));
			}
			
			for (int i : Srhs.dom().values){
				
				ArrayList<Link> map = r2l.get(new Integer(i));
				
				if (map.size() > 0){
					
					assert (map.size() == 1);
					int index = Arrays.binarySearch(Slhs.dom().values, map.get(0).leaf);
					Srhs.dom().inElement(store.level, Srhs, i, Slhs.dom().ProbRanges[index]);
				}
				else
					Srhs.dom().inElement(store.level, Srhs, i, new ProbabilityRange(0));
			}
			
		} while(store.propagationHasOccurred);
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

		Slhs.putModelConstraint(this, getConsistencyPruningEvent(Slhs));
		Srhs.putModelConstraint(this, getConsistencyPruningEvent(Srhs));

		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeConstraint() {

		Slhs.removeConstraint(this);
		Srhs.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {

        return false;

        /*
        // TODO: KRZYSZTOF
        // I think this procedure is not correct and it would be good to think about something correct.
        // Explanation: lhs and rhs domains may be equal at some point but later may not be equal.
        // If satisfied returns true at some point JaCoP will be able to remove this constraint for evaluation that
        // might not be correct since probabilities may change in later search , etc.

		for (int i = 0; i < Slhs.getSize(); i++){
			
			ArrayList<Link> map = l2r.get(new Integer(Slhs.dom().values[i]));
			
			if (map.size() > 0){
				
				assert (map.size() == 1);
				int index = Arrays.binarySearch(Srhs.dom().values, map.get(0).leaf);
				
				if (!Slhs.dom().ProbRanges[i].eq(Srhs.dom().ProbRanges[index]))
					return false;
			}
		}
		
		for (int i = 0; i < Srhs.getSize(); i++){
			
			ArrayList<Link> map = r2l.get(new Integer(Srhs.dom().values[i]));
			
			if (map.size() > 0){
				
				assert (map.size() == 1);
				int index = Arrays.binarySearch(Slhs.dom().values, map.get(0).leaf);
				
				if (!Srhs.dom().ProbRanges[i].eq(Srhs.dom().ProbRanges[index]))
					return false;
			}
		}
		
		return true;
		*/
	}

	@Override
	public String toString() {

		StringBuffer result = new StringBuffer( id() );
		
		result.append(" : SopCeqS( " + Slhs + " " + op.aOp + " " + C
				+ " == " + Srhs + ")");
		
		return result.toString();
	}

	@Override
	public void increaseWeight() {

		if (increaseWeight) {
			Slhs.weight++;
			Srhs.weight++;
		}
	}	
}