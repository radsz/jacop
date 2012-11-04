package org.jacop.stochastic.constraints;

import java.util.ArrayList;

import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.stochastic.core.Operator;
import org.jacop.stochastic.core.Operator.CompOp;
import org.jacop.stochastic.core.ProbabilityRange;
import org.jacop.stochastic.core.StochasticDomain;
import org.jacop.stochastic.core.StochasticVar;

/**
 * Implements the SopC constraint according to a reification probability factor
 * where S is a StochasticVar and C is a constant. The operation op can be 
 * "<", "<=", "==", ">" or ">=".
 */
public class SopC extends Constraint {

	static int IdNumber = 1;
	
	/**
	 * StochasticVar to be compared.
	 */
	public StochasticVar S;
	
	/**
	 * Specified Constant.
	 */
	public int C;
	
	/**
	 * Reification probaility factor, modelled as an IntVar.
	 */
	public IntVar pr;
	
	/**
	 * Resolution of the reification probability IntVar.
	 */
	public int res;
	
	/**
	 * Desired operation between S and C -
	 * "LESS", "LESS_EQUAL", "EQUAL", "GREATER" or "GREATER_EQUAL"
	 */
	public Operator op;
	
	/**
	 * This constructor creates a new SopC constraint.
	 * @param S : StochasticVar to be compared.
	 * @param C : Specified Constant.
	 * @param pr : Reification probaility factor, modelled as an IntVar.
	 * @param res : Resolution of the reification probability IntVar.
	 * @param op : Desired operation between S and C.
	 */
	public SopC(StochasticVar S, int C, IntVar pr, int res, Operator op){
		
		assert (op.cOp != CompOp.INVALID): "Invalid Operation";	
		
		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.numberArgs = (short)(2) ;
		this.S = S;
		this.C = C;
		this.pr = pr;
		this.res = res;	
		this.op = op;
	}
	
	@Override
	public ArrayList<Var> arguments() {
		
		ArrayList<Var> variables = new ArrayList<Var>(2);
		variables.add(S);
		variables.add(pr);

		return variables;
	}

	@Override
	public void consistency(Store store) {
		
		do{
			store.propagationHasOccurred = false;
		
			ProbabilityRange lhs = new ProbabilityRange(0);

			for (int i = 0; i < S.dom().values.length ; i++)
				if (op.doCompOp(S.dom().values[i],C))
					lhs.add(S.dom().ProbRanges[i]);

			int minP = (int)Math.floor(lhs.min*res);
			int maxP = (int)Math.ceil(lhs.max*res);

			//if (minP > maxP)
			//    throw Store.failException;

			// pr.dom().in(store.level, pr, (int)(lhs.min*res), (int)(lhs.max*res));		
			pr.dom().in(store.level, pr, minP, maxP);		
			
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
		
		S.putModelConstraint(this, getConsistencyPruningEvent(S));
		pr.putModelConstraint(this, getConsistencyPruningEvent(pr));

		store.addChanged(this);
		store.countConstraint();	
	}

	@Override
	public void removeConstraint() {

		S.removeConstraint(this);
		pr.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		
		// TODO, RADEK, it concerns all constraints. 
		// function satisfied can return true, ONLY if, no matter what changes 
		// this constraint will ALWAYS REMAIN satisfied. 
		if (!pr.singleton())
			return false;

		ProbabilityRange lhs = new ProbabilityRange(0);
		
		for (int i = 0; i < S.dom().values.length ; i++){

			if (op.doCompOp(S.dom().values[i],C)){
				
				if (!S.dom().ProbRanges[i].belongs(pr.min(), res))
					return false;
				lhs.add(S.dom().ProbRanges[i]);
			}
		}
		
		return lhs.belongs(pr.min(),res);
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );
		
		result.append(" : SopC( " + S + " " + op.cOp + " " + C
				+ "<=>" + pr + ")");
		
		return result.toString();
	}

	@Override
	public void increaseWeight() {
		
		if (increaseWeight) {
			S.weight++;
			pr.weight++;
		}	
	}

}
