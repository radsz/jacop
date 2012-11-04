package org.jacop.stochastic.core;

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Random;

import org.jacop.constraints.Constraint;
import org.jacop.core.Domain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Defines a Stochastic Variable and related operations on it.
 */

public class StochasticVar extends Var {

	/**
	 * Pointer to a current domain, which has stamp equal to store stamp.
	 */
	public DiscreteStochasticDomain domain;
			
	/**
	 * This is an empty constructor with no parameters.
	 */
	public StochasticVar() {
		
	}
	
	/**
	 * This constructor creates a StochasticVar in a given store with an empty 
	 * DiscreteStochasticDomain domain and an automatically generated name.
	 * @param store : Store in which the variable is created
	 */
	public StochasticVar(Store store) {
		
		this(store, store.getVariableIdPrefix() + idNumber++, new DiscreteStochasticDomain());
	}
	
	/**
	 * This constructor creates a StochasticVar that takes only a value of 0
	 * with default ProbabilityRange [0, 1].
	 * @param store : Store in which the variable is created
	 * @param name :  Name for the variable being created
	 */
	public StochasticVar(Store store, String name) {
		
		int[] values = {0};
		ProbabilityRange[] ProbRanges = {new ProbabilityRange()};
		commonInitialization(store, name, 
				new DiscreteStochasticDomain(values, ProbRanges));	
	}
	
	/**
	 * This constructor creates a StochasticVar in a given store, with a given 
	 * name and a given domain.
	 * @param store : Store in which the variable is created
	 * @param name :  Name for the variable being created
	 * @param dom : Domain of the variable being created
	 */
	public StochasticVar(Store store, String name, DiscreteStochasticDomain dom) {

		commonInitialization(store, name, dom);
	}
		
	/**
	 * This constructor creates a StochasticVar in a given store, with an 
	 * automatically generated name and a given domain.
	 * @param store : Store in which the variable is created
	 * @param dom : Domain of the variable being created
	 */
	public StochasticVar(Store store, DiscreteStochasticDomain dom) {
		
		this(store, store.getVariableIdPrefix() + idNumber++, dom);
	}
		
	/**
	 * This constructor creates a StochasticVar in a given store with a domain
	 * created according to the parameters given and the given name.
	 * @param store : Store in which the variable is created
	 * @param name :  Name for the variable being created
	 * @param values : Possible values of the domain  
	 * @param ProbRanges : Array of ProbabilityRange instances which 
	 * are associated with each possible value of the domain
	 */
	public StochasticVar(Store store, String name, int[] values, ProbabilityRange[] ProbRanges) {
		
		commonInitialization(store, name, new DiscreteStochasticDomain(values, ProbRanges));
	}
	
	/**
	 * This constructor creates a StochasticVar in a given store with a domain
	 * created according to the parameters given and an automatically generated name.
	 * @param store : Store in which the variable is created
	 * @param values : Possible values of the domain 
	 * @param ProbRanges : Array of ProbabilityRange instances which 
	 * are associated with each possible value of the domain
	 */
	public StochasticVar(Store store, int[] values, ProbabilityRange[] ProbRanges) {
		
		this(store, store.getVariableIdPrefix() + idNumber++, values, ProbRanges);
	}
	
	/**
	 * This constructor creates a StochasticVar in a given store with a domain
	 * created according to the parameters given and the given name.
	 * @param store : Store in which the variable is created
	 * @param name :  Name for the variable being created
	 * @param values : Possible values of the domain  
	 * @param minVals: Lower bounds of the ProbabilityRange instances which 
	 * are associated with each possible value of the domain
	 * @param maxVals: Upper bounds of the ProbabilityRange instances which 
	 * are associated with each possible value of the domain
	 */
	public StochasticVar(Store store, String name, int[] values, double[] minVals, double[] maxVals){
		
		this(store, name, new DiscreteStochasticDomain(values, minVals, maxVals));
	}
	
	/**
	 * This constructor creates a StochasticVar in a given store with a domain
	 * created according to the parameters given and an automatically generated name.
	 * @param store : Store in which the variable is created
	 * @param values : Possible values of the domain
	 * @param minVals: Lower bounds of the ProbabilityRange instances which 
	 * are associated with each possible value of the domain
	 * @param maxVals: Upper bounds of the ProbabilityRange instances which 
	 * are associated with each possible value of the domain
	 */
	public StochasticVar(Store store, int[] values, double[] minVals, double[] maxVals){
		
		this(store,store.getVariableIdPrefix() + idNumber++,
				new DiscreteStochasticDomain(values, minVals, maxVals));
	}
	
	/**
	 * This constructor creates a StochasticVar with a given name as obtained 
	 * by an arithmetic operation between a StochasticVar and an IntVar with 
	 * default [0,1] ProbabilityRange instances for the possible values.
	 * @param store : Store in which the variable is created
	 * @param name : Name for the variable being created
	 * @param S : StochasticVar
	 * @param X : IntVar
	 * @param op : Arithmetic Operation between S and X
	 */
	public StochasticVar(Store store, String name, StochasticVar S, IntVar X, Operator op){
		
		commonInitialization(store, name, new DiscreteStochasticDomain(S, X, op));
	}
	
	/**
	 * This constructor creates a StochasticVar with an automatically generated
	 * name as obtained by an arithmetic operation between a StochasticVar and 
	 * an IntVar with default [0,1] ProbabilityRange instances for the possible values.
	 * @param store : Store in which the variable is created
	 * @param S : StochasticVar
	 * @param X : IntVar
	 * @param op : Arithmetic Operation between S and X
	 */
	public StochasticVar(Store store, StochasticVar S, IntVar X, Operator op){
		
		this(store,store.getVariableIdPrefix() + idNumber++, S, X, op);
	}
	
	/**
	 * This constructor creates a StochasticVar with a given name as obtained 
	 * by an arithmetic operation between two StochasticVar instances with 
	 * default [0,1] ProbabilityRange instances for the possible values.
	 * @param store : Store in which the variable is created
	 * @param name : Name for the variable being created
	 * @param S : StochasticVar
	 * @param R : StochasticVar
	 * @param op : Arithmetic Operation between S and R
	 */
	public StochasticVar(Store store, String name, StochasticVar S, StochasticVar R, Operator op){
		
		commonInitialization(store, name, new DiscreteStochasticDomain(S, R, op));
	}
	
	/**
	 * This constructor creates a StochasticVar with an automatically generated
	 * name as obtained by an arithmetic operation between two StochasticVar 
	 * instances with default [0,1] ProbabilityRange instances for the possible values.
	 * @param store : Store in which the variable is created
	 * @param S : StochasticVar
	 * @param R : StochasticVar
	 * @param op : Arithmetic Operation between S and R
	 */
	public StochasticVar(Store store, StochasticVar S, StochasticVar R, Operator op){
		
		this(store, store.getVariableIdPrefix() + idNumber++, S, R, op);
	}
	
	/**
	 * This constructor creates a StochasticVar with a set of possible values
	 * equal to the union of the set of possibles values of all the 
	 * StochasticVars from the specified list. The ProbabilityRanges instances
	 * of the possible values are all set to the default [0,1] range.
	 * @param store : Store in which the variable is created
	 * @param name : Name for the variable being created
	 * @param list : List of StochasticVars
	 */
	public StochasticVar(Store store, String name, StochasticVar[] list){
		
		int size = 0;
		
		for (int i = 0; i < list.length; i++) {
			size += list[i].getSize();
		}
		
		int[] values = new int[size];
		int counter = 0;
		
		for (int i = 0; i < list.length; i++) {
			for (int j = 0; j < list[i].getSize(); j++) {
				
				values[counter] = list[i].dom().values[j];
				counter++;
			}
		}
		
		commonInitialization(store, name, new DiscreteStochasticDomain(values));
	}
	
	/**
	 * This constructor creates a StochasticVar with a set of possible values
	 * equal to the union of the set of possibles values of all the 
	 * StochasticVars from the specified list. The ProbabilityRanges instances
	 * of the possible values are all set to the default [0,1] range.
	 * @param store : Store in which the variable is created
	 * @param name : Name for the variable being created
	 * @param list : List of StochasticVars
	 */
	public StochasticVar(Store store, String name, StochasticVar[][] list){
		
		int size = 0;
		
		for (int i = 0; i < list.length; i++) 
			for (int j = 0; j < list[i].length; j++)
				size += list[i][j].getSize();
		
		
		int[] values = new int[size];
		int counter = 0;
		
		for (int i = 0; i < list.length; i++) {
			for (int j = 0; j < list[i].length; j++) {
				for (int k = 0; k < list[i][j].getSize(); k++) {
				
					values[counter] = list[i][j].dom().values[k];
					counter++;
				}
			}
		}
		
		commonInitialization(store, name, new DiscreteStochasticDomain(values));
	}
	
	/**
	 * This constructor generates a StochasticVar with random attributes.
	 * @param store : Store in which the variable is created
	 * @param name : Name for the variable being created
	 * @param StochasticConstant : if true generate a StochasticConstant, else
	 * generate a StochasticVariable
	 * @param size : Number of randomly generated possible values
	 * @param minVal : Lower Bound of randomly generated possible values
	 * @param maxVal : Upper Bound of randomly generated possible values
	 */
	public StochasticVar(Store store, String name, boolean StochasticConstant, int size, int minVal, int maxVal) {
		
		Random gen = new Random();
		DecimalFormat form = new DecimalFormat("#.##");

		int[] values = new int[size];
		ProbabilityRange[] ProbRanges = new ProbabilityRange[size];
		
		 ArrayList<Integer> l = new ArrayList<Integer>();
	     for(int i = minVal; i <= maxVal; i++) 
	       l.add(i);
	     Collections.shuffle(l);
	     
	     for (int i = size-1; i >= 0; i--)
				values[i] = l.get(i);
		
		if (StochasticConstant) {
			
			/*
			 * Generate random probabilities which sum to 1.
			 */
			
			double total = 1;
			double sum = 0;
			
			for (int i = size-1; i > 0; i--) {
				
				double tmp = Double.valueOf(form.format(gen.nextDouble()*total));
				sum += tmp;
				total -= tmp;
				ProbRanges[i] = new ProbabilityRange(tmp);
			}
			ProbRanges[0] = new ProbabilityRange(Double.valueOf(form.format(1 - sum)));
			
			if (size == 1)
				ProbRanges[0] = new ProbabilityRange(1);
		}
		
		else {
			
			/*
			 * Generate random ProbabilityRanges such that there is atleast 
			 * one valid distribution most times. 
			 */
			
			double total1 = 1;
			double sum1 = 0;
			
			double total2 = 1;
			double sum2 = 0;
			
			double minP, maxP, tmp1, tmp2;

			for (int i = size-1; i > 0; i--) {
				
				tmp1 = Double.valueOf(form.format(gen.nextDouble()*total1));
				sum1 += tmp1;
				total1 -= tmp1;
				
				tmp2 = Double.valueOf(form.format(gen.nextDouble()*total2));
				sum2 += tmp2;
				total2 -= tmp2;
							
				minP = (tmp1 < tmp2) ? tmp1 : tmp2;
				maxP = (tmp1 >= tmp2) ? tmp1 : tmp2;
				
				ProbRanges[i] = new ProbabilityRange(minP, maxP);
			}
			
			tmp1 = Double.valueOf(form.format(1 - sum1));
			tmp2 = Double.valueOf(form.format(1 - sum2));

			minP = (tmp1 < tmp2) ? tmp1 : tmp2;
			maxP = (tmp1 >= tmp2) ? tmp1 : tmp2;
			
			ProbRanges[0] = new ProbabilityRange(minP, maxP);
		}
		
		commonInitialization(store, name, new DiscreteStochasticDomain(values, ProbRanges));
	}
	
	/**
	 * This constructor generates a StochasticVar with random attributes.
	 * @param store : Store in which the variable is created
	 * @param name : Name for the variable being created
	 * @param seed : Seed for the random generator
	 * @param StochasticConstant : if true generate a StochasticConstant, else
	 * generate a StochasticVariable
	 * @param size : Number of randomly generated possible values
	 * @param minVal : Lower Bound of randomly generated possible values
	 * @param maxVal : Upper Bound of randomly generated possible values
	 */
	public StochasticVar(Store store, String name, int seed, boolean StochasticConstant, int size, int minVal, int maxVal) {
		
		Random gen = new Random(seed);
		DecimalFormat form = new DecimalFormat("#.#");

		int[] values = new int[size];
		ProbabilityRange[] ProbRanges = new ProbabilityRange[size];
		
		 ArrayList<Integer> l = new ArrayList<Integer>();
	     for(int i = minVal; i <= maxVal; i++) 
	       l.add(i);
	     Collections.shuffle(l, gen);
	     
	     for (int i = size-1; i >= 0; i--)
				values[i] = l.get(i);
		
		if (StochasticConstant) {
			
			/*
			 * Generate random probabilities which sum to 1.
			 */
			
			double total = 1;
			double sum = 0;
			
			for (int i = size-1; i > 0; i--) {
				
				double tmp = Double.valueOf(form.format(gen.nextDouble()*total));
				sum += tmp;
				total -= tmp;
				ProbRanges[i] = new ProbabilityRange(tmp);
			}
			ProbRanges[0] = new ProbabilityRange(Double.valueOf(form.format(1 - sum)));
			
			if (size == 1)
				ProbRanges[0] = new ProbabilityRange(1);
		}
		
		else {
			
			/*
			 * Generate random ProbabilityRanges such that there is atleast 
			 * one valid distribution most times. 
			 */
			
			double total1 = 1;
			double sum1 = 0;
			
			double total2 = 1;
			double sum2 = 0;
			
			double minP, maxP, tmp1, tmp2;

			for (int i = size-1; i > 0; i--) {
				
				tmp1 = Double.valueOf(form.format(gen.nextDouble()*total1));
				sum1 += tmp1;
				total1 -= tmp1;
				
				tmp2 = Double.valueOf(form.format(gen.nextDouble()*total2));
				sum2 += tmp2;
				total2 -= tmp2;
							
				minP = (tmp1 < tmp2) ? tmp1 : tmp2;
				maxP = (tmp1 >= tmp2) ? tmp1 : tmp2;
				
				ProbRanges[i] = new ProbabilityRange(minP, maxP);
			}
			
			tmp1 = Double.valueOf(form.format(1 - sum1));
			tmp2 = Double.valueOf(form.format(1 - sum2));

			minP = (tmp1 < tmp2) ? tmp1 : tmp2;
			maxP = (tmp1 >= tmp2) ? tmp1 : tmp2;
			
			ProbRanges[0] = new ProbabilityRange(minP, maxP);
		}
		
		commonInitialization(store, name, new DiscreteStochasticDomain(values, ProbRanges));
	}
	
	/**
	 * This method performs common initialization for all the contructors.
	 * @param store : Store in which the variable is created  
	 * @param name : Name for the variable being created 
	 * @param dom : Domain of the variable being created
	 */
	private void commonInitialization(Store store, String name, DiscreteStochasticDomain dom) {
		
		dom.searchConstraints = new ArrayList<Constraint>();
		dom.modelConstraints = new Constraint[StochasticDomain.eventsInclusion.length][];
		dom.modelConstraintsToEvaluate = new int[StochasticDomain.eventsInclusion.length];

		assert (name.lastIndexOf(" ") == -1) : "Name can not contain space character";
		
		id = name;
	    domain = dom;
		domain.stamp = 0;
		index = store.putVariable(this);
		this.store = store;
	}
	
	public void remove(int removedLevel) {
		domain.removeLevel(removedLevel, this);		
	}

	@Override
	public DiscreteStochasticDomain dom() {
		return domain;
	}

	@Override
	public int getSize() {
		return domain.getSize();
	}

	@Override
	public boolean isEmpty() {
		return domain.isEmpty();
	}
	
	/**
	 * This method compares 2 StochasticVar instances.
	 * @param var : StochasticVar to be compared
	 * @return true if the domains of the 2 StochasticVars are equal
	 */
	public boolean eq(StochasticVar var) {
		return domain.eq(var.dom());
	}

	@Override
	public void putModelConstraint(Constraint c, int pruningEvent) {

		// If variable is a singleton then it will not be put in the model.
		// It will be put in the queue and evaluated only once in the queue. 
		// If constraint is consistent for a singleton then it will remain 
		// consistent from the point of view of this variable.
		//if (singleton())
			//return;

		// if Event is NONE then constraint is not being attached, it will 
		// be only evaluated once, as after imposition it is being put in the constraint 
		// queue.
		
		if (pruningEvent == Domain.NONE) {
			return;
		}

		domain.putModelConstraint(store.level, this, c, pruningEvent);

		store.recordChange(this);
		
	}

	@Override
	public void putSearchConstraint(Constraint c) {
		
		if (singleton())
			return;

		domain.putSearchConstraint(store.level, this, c);

		store.recordChange(this);
		
	}

	@Override
	public void removeConstraint(Constraint c) {
		
		if (singleton())
			return;

		int i = domain.searchConstraintsToEvaluate - 1;
		for (; i >= 0; i--)
			if (domain.searchConstraints.get(i) == c)
				domain.removeSearchConstraint(store.level, this, i, c);

		if (i == -1)
			domain.removeModelConstraint(store.level, this, c);

		store.recordChange(this);
	}

	@Override
	public boolean singleton() {
		return domain.singleton();
	}

	@Override
	public int sizeConstraints() {
		return domain.sizeConstraints();
	}

	@Override
	public int sizeConstraintsOriginal() {
		return domain.sizeConstraintsOriginal();
	}

	@Override
	public int sizeSearchConstraints() {
		return domain.searchConstraintsToEvaluate;
	}

	@Override
	public int level() {
		return domain.stamp;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer(id);
		
		if (domain.singleton())
			result.append(" = ");
		else
			result.append("::");
			
		result.append(domain.toString());
		return result.toString();
		
	}
	
	@Override
	public String toStringFull() {
		StringBuffer result = new StringBuffer(id);
		result.append(domain.toStringFull());
		return result.toString();
	}

	@Override
	public void domainHasChanged(int event) {
		
		assert ((event == StochasticDomain.ANY && !singleton()) || 
				(event == StochasticDomain.BOUND && !singleton()) ||
				(event == StochasticDomain.GROUND && singleton())) : "Wrong event generated";
		
		store.addChanged(this, event, Integer.MIN_VALUE);
	}

	@Override
	public void putConstraint(Constraint c) {
		putModelConstraint(c, StochasticDomain.ANY);		
	}

}
