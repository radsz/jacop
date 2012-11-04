package org.jacop.stochastic.constraints;

import java.util.ArrayList;
import java.util.Arrays;

import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.stochastic.core.ProbabilityRange;
import org.jacop.stochastic.core.StochasticDomain;
import org.jacop.stochastic.core.StochasticVar;

/**
 * Connects the ProbabilityRange instances of a subset of values that
 * a StochasticVar can take to IntVars according to a given resolution.
 */
public class PrOfElement extends Constraint {

	static int IdNumber = 1;
	
	/**
	 * StochasticVar whose ProbabilityRange instances are to be connected 
	 * to IntVars.
	 */
	public StochasticVar S;
	
	/**
	 * Subset of values that S can take.
	 */
	public int[] values;
	
	/**
	 * Corresponding probability IntVar instances. 
	 */
	public IntVar[] Ps;
	
	/**
	 * Required resolution.
	 */
	public int res;
	
	/**
	 * This constructor creates a new PrOfElement constraint.
	 * @param S : StochasticVar
	 * @param values : Subset of values that S can take
	 * @param Ps : Corresponding probability IntVar instances
	 * @param res : Required resolution
	 */
	public PrOfElement(StochasticVar S, int[] values, IntVar[] Ps, int res){
		
		assert (values.length == Ps.length) : 
			"Dimension mismatch of input parameters.";
		
		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.numberArgs = (short) (Ps.length + 1) ;
		this.S = S;
		this.values = values;
		this.Ps = Ps;
		this.res = res;	
	}
	
	/**
	 * This constructor creates a new PrOfElement constraint.
	 * @param S : StochasticVar
	 * @param p : Corresponding probability IntVar instance
	 * @param res : Required resolution
	 */
	public PrOfElement(StochasticVar S, IntVar p, int res){
		
		assert (values.length == Ps.length) : 
			"Dimension mismatch of input parameters.";
		
		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.numberArgs = (short) (2) ;
		this.S = S;
		this.values = S.dom().values;
		this.Ps = new IntVar[1];
		this.Ps[0] = p;
		this.res = res;	
	}
	
	@Override
	public ArrayList<Var> arguments() {
		
		ArrayList<Var> variables = new ArrayList<Var>(Ps.length + 1);

		variables.add(S);
		
		for (IntVar V : Ps)
			variables.add(V);
		
		return variables;
	}

	@Override
	public void consistency(Store store) {

	    // System.out.println("Consistency for " + S + ", "+ Arrays.asList(Ps));

        do {
	    store.propagationHasOccurred = false;
			
            ProbabilityRange[] newProbabilityRanges = new ProbabilityRange[values.length];

	    for (int i=0; i < values.length; i++){
				
		// TODO, Radek, values inside S will not change so why can not 
		// values and vars in this constraint be arranged in the same 
		// manner as values inside Stochastic var.
		int index = Arrays.binarySearch(S.dom().values, values[i]);				
				
		/*
		 * Constraint fails if the value is not present in the 
		 * domain of S 
		 */
		if (index < 0)
		    // TODO, Should not this be rather a failure of proper constraint imposition,
		    // instead of search failure?
		    throw Store.failException;
		else {
		    ProbabilityRange pRange = S.dom().ProbRanges[index];
                    //System.out.println(S + " and its pRange["+index+"] = " + pRange);

                    // Seems to be too strict...
		    // int minP = (int)Math.round(Math.ceil(pRange.min*res));
		    // int maxP = (int)Math.round(Math.floor(pRange.max*res));

                    // Most relaxed rounding to not loose any solutions; can be replaced by Math.round in both...
                    int minP = (int)Math.floor(pRange.min*res);
                    int maxP = (int)Math.ceil(pRange.max*res);

                    //System.out.println(S + "   " + S.dom().values[index] + ", " + pRange.min +".."+pRange.max + " = {"+minP+".."+maxP+"}");

//					if (minP > maxP) {
//                        //System.out.println(S + "   " + S.dom().values[index] + ", " + pRange.min +".."+pRange.max + " = {"+minP+".."+maxP+"}");
//                        if (pRange.eq())
//                            maxP = minP;
//                        else
//					        throw Store.failException;
//                    }

                    //System.out.println(Ps[i] +" <- {" + minP+".."+maxP+"}");

		    Ps[i].domain.in(store.level, Ps[i], minP, maxP);

                    //System.out.println("OK");

                    newProbabilityRanges[i] = new ProbabilityRange(((double)Ps[i].min())/res, ((double)Ps[i].max())/res);

		}
	    }	

            //System.out.println (S + " <= " + Arrays.asList(newProbabilityRanges));

	    S.dom().inElement(store.level, S, S.dom().values, newProbabilityRanges);

            //System.out.println("OK");

	} while(store.propagationHasOccurred);

        //System.out.println("EXIT");

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

		for (Var V : Ps)
			V.putModelConstraint(this, getConsistencyPruningEvent(V));

		store.addChanged(this);
		store.countConstraint();	
	}

	@Override
	public void removeConstraint() {
		
		S.removeConstraint(this);
		for (int i = 0; i < Ps.length; i++) {
			Ps[i].removeConstraint(this);
		}
	}

	@Override
	public boolean satisfied() {
	    
	    for (int i=0; i < values.length; i++){
			
		int index = Arrays.binarySearch(S.domain.values, values[i]);
			
		if (index < 0)
		    return false;
		else { // index >=0
		    ProbabilityRange pRange = S.domain.ProbRanges[index];
		    if (!Ps[i].singleton())
			return false;
		    else if (Ps[i].min() < (int)(pRange.min*res) ||
			     Ps[i].min() > (int)(pRange.max*res))
			return false;
		}
	    }
	    return true;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );
		
		result.append(" : PrOfElement( " + S + ", ");
		for (int i = 0; i < Ps.length; i++) {
			result.append(values[i]+" :");
			result.append( Ps[i] );
			if (i < Ps.length - 1)
				result.append(", "); 
		}
		result.append(")");
		return result.toString();
		
	}

	@Override
	public void increaseWeight() {
		
		if (increaseWeight) {
			S.weight++;
			for (Var v : Ps) v.weight++;
		}	
	}

}
