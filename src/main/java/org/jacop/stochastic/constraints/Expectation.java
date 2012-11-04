package org.jacop.stochastic.constraints;

import java.util.ArrayList;
import java.util.HashMap;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.SumWeight;
import org.jacop.stochastic.constraints.PrOfElement;
import org.jacop.stochastic.core.StochasticVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

public class Expectation extends DecomposedConstraint {

    ArrayList<Constraint> constraints;

    /**
     * IntVar[] equivalent of the StochasticVar ProbabilityRange[] attribute.
     */
    public IntVar prS[];

    /**
     * Possible values that the StochasticVar can take.
     */
    public int values[];

    /**
     * Expectation of the StochasticVar 
     */
    public IntVar E;

    /**
     * StochasticVar for computation 
     */
    public StochasticVar s;

    /**
     * Resolution for probability reification, if given 
     */
    public int res = -1;

    /**
     * @param s Stochastic variable to compute expected value 
     * @param E expected value
     * @param res resolution for probabilities
     */
    public Expectation(StochasticVar s, IntVar E, int res) {

	prS = new IntVar[s.dom().values.length];
	values = s.dom().values;
	this.E = E;
	this.res = res;
	this.s = s;

	constraints = new ArrayList<Constraint>();

    }
	

    /**
     * @param prS Probabilities
     * @param values Values of stochastic variables
     * @param E expected value
     */
    public Expectation(IntVar[] prS, int[] values, IntVar E) {

	commonInitialization(prS, values, E);
		
    }
	
    private void commonInitialization(IntVar[] prS, int[] values, IntVar E) {
		
	queueIndex = 1;

	assert ( prS.length == values.length );

	this.E = E;

	HashMap<IntVar, Integer> parameters = new HashMap<IntVar, Integer>();

	for (int i = 0; i < prS.length; i++) {

	    assert (prS[i] != null);
			
	    if (parameters.get(prS[i]) != null) {
		// variable ordered in the scope of the Sum Weight constraint.
		Integer coeff = parameters.get(prS[i]);
		Integer sumOfCoeff = coeff + values[i];
		parameters.put(prS[i], sumOfCoeff);
	    }
	    else
		parameters.put(prS[i], values[i]);

	}

	assert ( parameters.get(E) == null) : "Sum variable is used in both sides of SumWeight constraint.";

	this.prS = new IntVar[parameters.size()];
	this.values = new int[parameters.size()];

	int i = 0;
	for (IntVar var : parameters.keySet()) {
	    this.prS[i] = var;
	    this.values[i] = parameters.get(var);
	    i++;
	}
    }

    @Override
	public void imposeDecomposition(Store store) {

	if (res == -1)
	    decompose(store);

	else {

	    for (int i=0; i<prS.length; i++)
		prS[i] = new IntVar(store, 0, res);

	    constraints.add(new PrOfElement(s, values, prS, res));
	    constraints.add(new SumWeight(prS, values, E));
	     
	}

	for (Constraint c : constraints)
	    store.impose(c, queueIndex);
 
    }

    @Override
	public ArrayList<Constraint> decompose(Store store) {

        Constraint c = new SumWeight(prS, values, E);

        constraints = new ArrayList<Constraint>();
        constraints.add(c);

        return constraints;
    }
}

