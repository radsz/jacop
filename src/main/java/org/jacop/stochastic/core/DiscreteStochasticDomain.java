package org.jacop.stochastic.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.jacop.constraints.Constraint;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Defines a DiscreteStochasticDomain and related operations on it. A 
 * DiscreteStochasticDomain has a set of values which it can take, each 
 * associated with a ProbabilityRange.
 */

public class DiscreteStochasticDomain extends StochasticDomain {

	/**
	 * Possible values of the DiscreteStochasticDomain instance.
	 */
	public int[] values;
		
	/**
	 * Array of ProbabilityRange instances which are associated with 
	 * each possible value of the domain.
	 */
	public ProbabilityRange[] ProbRanges;

	/**
	 * Previous domain used by this domain. The old domain is stored here
	 * and can be easily restored if necessary.
	 */
	public DiscreteStochasticDomain previousDomain;	
	
	/**
	 * Predefined empty domain so there is no need to constantly create it when
	 * needed.
	 */
	static public DiscreteStochasticDomain emptyDomain = new DiscreteStochasticDomain();
		
	/**
	 * This constructor creates an empty domain with null attributes.
	 */
	public DiscreteStochasticDomain() {
		values = null;
		ProbRanges = null;
	}
	
	/** This constructor creates a new instance of DiscreteStochasticDomain.
	 * @param values : Possible values of the DiscreteStochasticDomain 
	 * instance  
	 * @param ProbRanges : Array of ProbabilityRange instances which 
	 * are associated with each possible value of the domain
	 */
	public DiscreteStochasticDomain(int[] values, ProbabilityRange[] ProbRanges) {
		
		commonInitialization(values, ProbRanges);	
	}
	
	/** This constructor creates a new instance of DiscreteStochasticDomain 
	 * with default ProbabiltyRange of [0,1] for all the possible values.
	 * @param values : Possible values of the DiscreteStochasticDomain 
	 * instance.
	 */
	public DiscreteStochasticDomain(int[] values) {
		
		ProbabilityRange[] ProbRanges = new ProbabilityRange[values.length];
		for (int i = 0; i < values.length; i++)
			ProbRanges[i] = new ProbabilityRange();
		
		commonInitialization(values, ProbRanges);
	}
	
	/**
	 * This constructor creates a new instance of DiscreteStochasticDomain. 
	 * @param values : Possible values of the DiscreteStochasticDomain 
	 * instance
	 * @param minPs : Lower bounds of the ProbabilityRange instances which 
	 * are associated with each possible value of the domain.
	 * @param maxPs : Upper bounds of the ProbabilityRange instances which 
	 * are associated with each possible value of the domain
	 */
	public DiscreteStochasticDomain(int[] values, double[] minPs, double[] maxPs) {

		this.values = values;
		ProbRanges = new ProbabilityRange[values.length];
		
		for (int i = 0; i < values.length; i++)
            if (minPs[i] <= maxPs[i])
                ProbRanges[i] = new ProbabilityRange(minPs[i], maxPs[i]);
            else
                throw new IllegalArgumentException("\nMin value (" + minPs[i] + ") greater than max (" + maxPs[i] + ") in stochastic variable");

		commonInitialization(values, ProbRanges);
	}
	
	/**
	 * This constructor creates a new instance of DiscreteStochasticDomain as
	 * obtained by an arithmetic operation between a DiscreteStochasticDomain
	 * and an IntDomain. This constructor instantiates the possible values that
	 * the domain can take with default [0,1] ProbabilityRange instances.
	 * @param Sdom : DiscreteStochasticDomain
	 * @param Xdom : IntDomain
	 * @param op : Arithmetic Operation between Sdom and Xdom
	 */
	public DiscreteStochasticDomain(DiscreteStochasticDomain Sdom, IntDomain Xdom, Operator op) {
		
		int lXdom = Xdom.getSize();
		int lSdom = Sdom.values.length;
		int[] v = new int[lXdom*lSdom];
		ProbabilityRange[] pRanges = new ProbabilityRange[lXdom*lSdom];
		
		for (int i = 0; i < lXdom; i++) {
			for (int j = 0; j < lSdom; j++) {
				v[lSdom*i + j] = op.doArithOp(Xdom.getElementAt(i), Sdom.values[j]);
				pRanges[lSdom*i + j] = new ProbabilityRange();
			}
		}
		
		commonInitialization(v, pRanges);
	}
	
	/**
	 * This constructor creates a new instance of DiscreteStochasticDomain as
	 * obtained by an arithmetic operation between a StochasticVar and an IntVar.
	 * This constructor instantiates the possible values that the domain can 
	 * take with default [0,1] ProbabilityRange instances.
	 * @param S : StochasticVar
	 * @param X : IntVar
	 * @param op : Arithmetic Operation between S and X
	 */
	public DiscreteStochasticDomain(StochasticVar S, IntVar X, Operator op) {
		
		this(S.dom(), X.dom(), op);
	}
	
	/**
	 * This constructor creates a new instance of DiscreteStochasticDomain as
	 * obtained by an arithmetic operation between two DiscreteStochasticDomain
	 * instances. This constructor instantiates the possible values that the 
	 * domain can take with default [0,1] ProbabilityRange instances.
	 * @param Sdom : DiscreteStochasticDomain 1
	 * @param Rdom : DiscreteStochasticDomain 2
	 * @param op : Arithmetic Operation between Sdom and Rdom
	 */
	public DiscreteStochasticDomain(DiscreteStochasticDomain Sdom, DiscreteStochasticDomain Rdom, Operator op) {
		
		int lRdom = Rdom.values.length;
		int lSdom = Sdom.values.length;
		int[] v = new int[lRdom*lSdom];
		ProbabilityRange[] pRanges = new ProbabilityRange[lRdom*lSdom];
		
		for (int i = 0; i < lRdom; i++){
			for (int j = 0; j < lSdom; j++){
				v[lSdom*i + j] = op.doArithOp(Rdom.values[i], Sdom.values[j]);
				pRanges[lSdom*i + j] = new ProbabilityRange();
			}
		}
		
		commonInitialization(v, pRanges);
	}
	
	/**
	 * This constructor creates a new instance of DiscreteStochasticDomain as
	 * obtained by an arithmetic operation between two StochasticVar instances.
	 * This constructor instantiates the possible values that the domain can 
	 * take with default [0,1] ProbabilityRange instances.
	 * @param S : StochasticVar 1
	 * @param R : StochasticVar 2
	 * @param op : Arithmetic Operation between S and R
	 */
	public DiscreteStochasticDomain(StochasticVar S, StochasticVar R, Operator op) {
		
		this(S.dom(), R.dom(), op);
	}

	/**
	 * This method performs common initialization for all the contructors.
	 * @param values : Possible values of the DiscreteStochasticDomain instance  
	 * @param ProbRanges : Array of ProbabilityRange instances which are 
	 * associated with each possible value of the domain
	 */
	private void commonInitialization(int[] values, ProbabilityRange[] ProbRanges) {

		assert ProbRanges.length == values.length;
		
		this.values = values;
		this.ProbRanges = ProbRanges;		
		trimDomain();

		searchConstraints = null;
		searchConstraintsToEvaluate = 0;
		previousDomain = null;
		searchConstraintsCloned = false;
	}
	
	/**
	 * This method trims the domain for duplicate values. A union operation is
	 * performed between the ProbabilityRanges of duplicate values.
	 */
	private void trimDomain(){
		
		int[] a = values;
		
		Integer[] A = new Integer[a.length];
		for (int i=0; i < a.length; i++)
			A[i] = new Integer(a[i]);
		
		List<Integer> l = Arrays.asList(A);
		Set<Integer> s = new HashSet<Integer>(l);
		Integer[] B = new Integer[s.size()];
		s.toArray(B);
		int[] b = new int[s.size()];
		
		for (int i=0; i<B.length; i++)
			b[i] = B[i].intValue();
		
		Arrays.sort(b);
		ProbabilityRange[] newProbRanges = new ProbabilityRange[b.length];
		
		for (int i=0; i < b.length; i++){
			
			newProbRanges[i] = new ProbabilityRange(1,0);			
			
			for (int j=0; j < a.length; j++)
				if(b[i]==a[j])
					newProbRanges[i].union(ProbRanges[j]);
		}
		setDomain(b, newProbRanges);
	}
	
	/**
	 * This method sets the attributes of the DiscreteStochasticDomain instance.
	 * @param values : Possible values of the DiscreteStochasticDomain instance  
	 * @param ProbRanges : Array of ProbabilityRange instances which are 
	 * associated with each possible value of the domain
	 */
	public void setDomain(int[] values, ProbabilityRange[] ProbRanges){
	
		this.values = values;
		this.ProbRanges = ProbRanges;
	}
	
	@Override
	public void clear() {
		values = null;
		ProbRanges = null;
	}
	
	@Override
	public DiscreteStochasticDomain cloneLight() {
		
		if (!isEmpty())
			return new DiscreteStochasticDomain(values, ProbRanges);
		else
			return new DiscreteStochasticDomain();	
	}

	@Override
	public Domain clone() {

		DiscreteStochasticDomain cloned;
		
		if (!isEmpty())
			cloned = new DiscreteStochasticDomain(values, ProbRanges);
		else
			cloned = new DiscreteStochasticDomain();
		
		cloned.stamp = stamp;
		cloned.previousDomain = previousDomain;

		cloned.searchConstraints = searchConstraints;
		cloned.searchConstraintsToEvaluate = searchConstraintsToEvaluate;

		cloned.modelConstraints = modelConstraints;	
		cloned.modelConstraintsToEvaluate = modelConstraintsToEvaluate;

		cloned.searchConstraintsCloned = searchConstraintsCloned;

		return cloned;	
	}

	@Override
	public ValueEnumeration valueEnumeration() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int getSize() {
		return values.length;
	}

	@Override
	public boolean isEmpty() {
		return values == null;
	}

	@Override
	public void removeModelConstraint(int storeLevel, Var var, Constraint C) {
		
		if (stamp < storeLevel) {

			DiscreteStochasticDomain result = this.cloneLight();

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((StochasticVar)var).domain = result;

			result.removeModelConstraint(storeLevel, var, C);
			return;
		}

		int pruningEvent = GROUND;

		Constraint[] pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean isImposed = false;

			int i;

			for (i = modelConstraintsToEvaluate[pruningEvent] - 1; i >= 0; i--)
				if (pruningEventConstraints[i] == C) {
					isImposed = true;
					break;
				}

			// int pruningConstraintsToEvaluate =
			// modelConstraintsToEvaluate[pruningEvent];

			if (isImposed) {

				if (i != modelConstraintsToEvaluate[pruningEvent] - 1) {

					modelConstraints[pruningEvent][i] = modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1];

					modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1] = C;
				}

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]--;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

				return;

			}

		}

		pruningEvent = BOUND;

		pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean isImposed = false;

			int i;

			for (i = modelConstraintsToEvaluate[pruningEvent] - 1; i >= 0; i--)
				if (pruningEventConstraints[i] == C) {
					isImposed = true;
					break;
				}

			if (isImposed) {

				if (i != modelConstraintsToEvaluate[pruningEvent] - 1) {

					modelConstraints[pruningEvent][i] = modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1];

					modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1] = C;
				}

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]--;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

				return;

			}

		}

		pruningEvent = ANY;

		pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean isImposed = false;

			int i;

			for (i = modelConstraintsToEvaluate[pruningEvent] - 1; i >= 0; i--)
				if (pruningEventConstraints[i] == C) {
					isImposed = true;
					break;
				}

			// int pruningConstraintsToEvaluate =
			// modelConstraintsToEvaluate[pruningEvent];

			if (isImposed) {

				if (i != modelConstraintsToEvaluate[pruningEvent] - 1) {

					modelConstraints[pruningEvent][i] = modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1];

					modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1] = C;
				}

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]--;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;
			}
		}		
	}

	@Override
	public void removeSearchConstraint(int storeLevel, Var var, int position,
			Constraint C) {
		
		if (stamp < storeLevel) {

			DiscreteStochasticDomain result = this.cloneLight();

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((StochasticVar)var).domain = result;

			result.removeSearchConstraint(storeLevel, var, position, C);
			return;
		}

		assert (stamp == storeLevel);

		if (position < searchConstraintsToEvaluate) {

			searchConstraints.set(position, searchConstraints
					.get(searchConstraintsToEvaluate - 1));
			searchConstraints.set(searchConstraintsToEvaluate - 1, C);
			searchConstraintsToEvaluate--;
		}
	}

	/**
	 * This method checks whether the DiscreteStochasticDomain instance 
	 * corresponds to a stochastic variable or a stochastic constant.
	 * @return true, if all the corresponding ProbabilityRange intances 
	 * are singletons, false otherwise.
	 */
	public boolean singleton() {
		
		for (int i = 0; i < getSize(); i++)
			if (!ProbRanges[i].singleton())
				return false;
		
		return true;
	}
	
	@Override
	public boolean singleton(Domain value) {
		
		if (!singleton())
			return false;
		
		if (isEmpty())
			return false;
		
		if (!value.singleton())
			throw new IllegalArgumentException("An argument should be a singleton domain");

		assert (value instanceof DiscreteStochasticDomain) : "Can not compare Discrete" +
				"Stochastic domains with other types of domains.";
		
		DiscreteStochasticDomain domain = (DiscreteStochasticDomain) value;
		
		return (eq(domain));
	}

	/**
	 * This method compares 2 DiscreteStochasticDomain instances.
	 * @param domain : DiscreteStochasticDomain to be compared.
	 * @return true if the 2 domains are equal.
	 */
	public boolean eq(DiscreteStochasticDomain domain) {
		
		if (domain.isEmpty() && isEmpty())
			return true;
		
		if (domain.getSize() != getSize())
			return false;
				
		for (int i = 0; i < getSize(); i++)
			if ((values[i] != domain.values[i]) || (!ProbRanges[i].eq(domain.ProbRanges[i])))
				return false;
					
		return true;	
	}
	
	/**
	 * This method compares 2 DiscreteStochasticDomain instances.
	 * @param values : Possible values of the DiscreteStochasticDomain instance.
	 * @param minPs : Lower bounds of the ProbabilityRange instances which 
	 * are associated with each possible value of the domain.
	 * @param maxPs : Upper bounds of the ProbabilityRange instances which 
	 * are associated with each possible value of the domain.
	 * @return true if the 2 domains are equal.
	 */
	public boolean eq(int[] values, double[] minPs, double[] maxPs) {
		
		return eq(new DiscreteStochasticDomain(values, minPs, maxPs));	
	}
	
	/**
	 * This method compares 2 DiscreteStochasticDomain instances.
	 * @param values : Possible values of the DiscreteStochasticDomain instance.
	 * @param ProbRanges : Array of ProbabilityRange instances which are 
	 * associated with each possible value of the domain
	 * @return true if the 2 domains are equal.
	 */
	public boolean eq(int[] values, ProbabilityRange[] ProbRanges) {
	
		return eq(new DiscreteStochasticDomain(values, ProbRanges));
	}
	
	/**
	 * This method compares the ProbabilityRange of a specific element of the 
	 * domain with the given ProbabilityRange.
	 * @param value : Specified Value
	 * @param r : Specified ProbabilityRange
	 * @return true if the specified value has ProbabilityRange equal to the
	 * specified ProbabilityRange.
	 */
	public boolean eqElement(int value, ProbabilityRange r) {
		
		int index = Arrays.binarySearch(values, value);
		
		if (index < 0)
			return false;
		else {
            //System.out.println(ProbRanges[index] + " ? " + r);

            return (ProbRanges[index].eq(r));
        }
    }
	
	@Override
	public int noConstraints() {
		
		return searchConstraintsToEvaluate 
		+ modelConstraintsToEvaluate[GROUND]
		+ modelConstraintsToEvaluate[BOUND]
		+ modelConstraintsToEvaluate[ANY];
	}

	@Override
	public String toString() {
		
		StringBuffer S = new StringBuffer("");		
		assert getSize() == ProbRanges.length;

		S.append ("{");

		for (int i = 0; i < getSize(); i++) {
			// S.append("\n Value: "+ values[i] + ", Probabilty Range: "+ ProbRanges[i]);
			S.append(values[i] + " ("+ ProbRanges[i]+")");
			if (i != getSize()-1)
			    S.append(", ");
		}

		S.append("}");
		return S.toString();
	}

	@Override
	public String toStringConstraints() {
		
		StringBuffer S = new StringBuffer("");

		for (Iterator<Constraint> e = searchConstraints.iterator(); e.hasNext();) {
			S.append(e.next().id());
			if (e.hasNext())
				S.append(", ");
		}
		return S.toString();		
	}

	@Override
	public String toStringFull() {
		
		StringBuffer result = new StringBuffer("");
		DiscreteStochasticDomain domain = this;

		do {
			result.append(toString()).append("(").append(domain.stamp()).append(") ");
			
			result.append("constraints: ");

			for (Iterator<Constraint> e = domain.searchConstraints.iterator(); e
					.hasNext();)
				result.append(e.next());

			if (domain.domainID() == DiscreteStochasticDomainID) {

				DiscreteStochasticDomain dom = (DiscreteStochasticDomain) domain;
				domain = dom.previousDomain;
			} 
			else {		
				// Other type.
			}

		} while (domain != null);

		return result.toString();
	}

	@Override
	public void removeLevel(int level, Var var) {
		
		assert (this.stamp <= level);

		if (this.stamp == level) {

			((StochasticVar)var).domain = this.previousDomain;
		}
		assert (var.level() < level);		
	}

	@Override
	public int domainID() {
		return DiscreteStochasticDomainID;
	}

	@Override
	public boolean isSparseRepresentation() {
		return false;
	}

	@Override
	public boolean isNumeric() {
		return true;
	}

	@Override
	public void putModelConstraint(int storeLevel, Var var, Constraint C,
			int pruningEvent) {
		
		if (stamp < storeLevel) {

			DiscreteStochasticDomain result = this.cloneLight();

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((StochasticVar)var).domain = result;

			result.putModelConstraint(storeLevel, var, C, pruningEvent);
			return;
		}

		Constraint[] pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean alreadyImposed = false;

			if (modelConstraintsToEvaluate[pruningEvent] > 0)
				for (int i = pruningEventConstraints.length - 1; i >= 0; i--)
					if (pruningEventConstraints[i] == C)
						alreadyImposed = true;

			int pruningConstraintsToEvaluate = modelConstraintsToEvaluate[pruningEvent];

			if (!alreadyImposed) {
				Constraint[] newPruningEventConstraints = new Constraint[pruningConstraintsToEvaluate + 1];

				System.arraycopy(pruningEventConstraints, 0,
						newPruningEventConstraints, 0,
						pruningConstraintsToEvaluate);
				newPruningEventConstraints[pruningConstraintsToEvaluate] = C;

				Constraint[][] newModelConstraints = new Constraint[3][];

				newModelConstraints[0] = modelConstraints[0];
				newModelConstraints[1] = modelConstraints[1];
				newModelConstraints[2] = modelConstraints[2];

				newModelConstraints[pruningEvent] = newPruningEventConstraints;

				modelConstraints = newModelConstraints;

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]++;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

			}

		} else {

			Constraint[] newPruningEventConstraints = new Constraint[1];

			newPruningEventConstraints[0] = C;

			Constraint[][] newModelConstraints = new Constraint[3][];

			newModelConstraints[0] = modelConstraints[0];
			newModelConstraints[1] = modelConstraints[1];
			newModelConstraints[2] = modelConstraints[2];

			newModelConstraints[pruningEvent] = newPruningEventConstraints;

			modelConstraints = newModelConstraints;

			int[] newModelConstraintsToEvaluate = new int[3];

			newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
			newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
			newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

			newModelConstraintsToEvaluate[pruningEvent] = 1;

			modelConstraintsToEvaluate = newModelConstraintsToEvaluate;
		}
	}

	@Override
	public void putSearchConstraint(int storeLevel, Var var, Constraint C) {
		
		if (!searchConstraints.contains(C)) {

			if (stamp < storeLevel) {

				DiscreteStochasticDomain result = this.cloneLight();

				result.modelConstraints = modelConstraints;

				result.searchConstraints = new ArrayList<Constraint>(
						searchConstraints.subList(0,
								searchConstraintsToEvaluate));
				result.searchConstraintsCloned = true;
				result.stamp = storeLevel;
				result.previousDomain = this;
				result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
				result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
				((StochasticVar)var).domain = result;

				result.putSearchConstraint(storeLevel, var, C);
				return;
			}

			if (searchConstraints.size() == searchConstraintsToEvaluate) {
				searchConstraints.add(C);
				searchConstraintsToEvaluate++;
			} else {
				// Exchange the first satisfied constraint with just added
				// constraint
				// Order of satisfied constraints is not preserved

				if (searchConstraintsCloned) {
					Constraint firstSatisfied = searchConstraints
							.get(searchConstraintsToEvaluate);
					searchConstraints.set(searchConstraintsToEvaluate, C);
					searchConstraints.add(firstSatisfied);
					searchConstraintsToEvaluate++;
				} else {
					searchConstraints = new ArrayList<Constraint>(
							searchConstraints.subList(0,
									searchConstraintsToEvaluate));
					searchConstraintsCloned = true;
					searchConstraints.add(C);
					searchConstraintsToEvaluate++;
				}
			}
		}
	}

	@Override
	public int sizeConstraintsOriginal() {
		
		DiscreteStochasticDomain domain = this;

		while (domain.domainID() == DiscreteStochasticDomainID) {

			DiscreteStochasticDomain dom = (DiscreteStochasticDomain) domain;

			if (dom.previousDomain != null)
				domain = dom.previousDomain;
			else
				break;
		}

		if (domain.domainID() == DiscreteStochasticDomainID)
			return (domain.modelConstraintsToEvaluate[0]
					+ domain.modelConstraintsToEvaluate[1] + domain.modelConstraintsToEvaluate[2]);
		else
			return domain.sizeConstraintsOriginal();		
	}

	@Override
	public void in(int storeLevel, Var var, Domain d) {
				
		DiscreteStochasticDomain dom = (DiscreteStochasticDomain)d;
		
		if (eq(dom))
			return;
		
		inElement(storeLevel, (StochasticVar)var, dom.values, dom.ProbRanges);
	}
	
	/**
	 * This method updates the domain such that the elements specified have 
	 * ProbabilityRanges 'in' the corresponding specified ProbabilityRanges. 
	 * The type of update is decided by the value of stamp. It informs the 
	 * variable of a change if it occurred. 
	 * @param storeLevel : Level of the store at which the update occurs
	 * @param S : Variable for which this domain is used
	 * @param el : Elements of S whose ProbabilityRanges are to be updated
	 * @param pRanges : ProbabilityRanges to which domain is updated
	 */
	public void inElement(int storeLevel, StochasticVar S, int[] el, ProbabilityRange[] pRanges) {
		
		if (eq(el, pRanges))
			return;
		
		assert (el.length == pRanges.length);
		
		for (int i=0; i < el.length; i++)
			inElement(storeLevel, S, el[i], pRanges[i]);
	}

	/**
	 * This method updates the domain such that the specified element has 
	 * ProbabilityRange 'in' the corresponding specified ProbabilityRange. 
	 * The type of update is decided by the value of stamp. It informs the 
	 * variable of a change if it occurred. 
	 * @param storeLevel : Level of the store at which the update occurs
	 * @param S : Variable for which this domain is used
	 * @param el : Element of S whose ProbabilityRange is to be updated
	 * @param r : ProbabilityRange to which domain is updated
	 */
	public void inElement (int storeLevel, StochasticVar S, int el, ProbabilityRange r) {
		
		if (eqElement(el, r))
			return;

        // CHANGE to avoid looping forever when no pruning is done but store thinks it has changed
        // case when the update covers current interval

	    int index = Arrays.binarySearch(values, el);

	    if (index < 0)
		throw failException;
	    // else if (ProbRanges[index].min > r.max || ProbRanges[index].max < r.min)
	    // 	throw failException;
	    else if (ProbRanges[index].min >= r.min && ProbRanges[index].max <= r.max)
	     	return;

		if (stamp == storeLevel) {
			
			//int index = Arrays.binarySearch(S.dom().values, el);
			
//			if (index < 0)
//				throw failException;
//			else
				ProbRanges[index].in(r);
		}
		
		else {
			
			assert stamp < storeLevel;
			
			DiscreteStochasticDomain result = cloneLight();
			//int index = Arrays.binarySearch(S.dom().values, el);
			
//			if (index < 0)
//				throw failException;
//			else

			result.ProbRanges[index].in(r);
			
			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			S.domain = result;	
		}

		if (S.dom().singleton()) {
			S.domainHasChanged(StochasticDomain.GROUND);
			return;
		} 
		else {
			S.domainHasChanged(StochasticDomain.BOUND);
			return;
		}
	}
	

/**
	 * This method updates the domain such that the elements specified have 
	 * ProbabilityRanges equal to the corresponding specified ProbabilityRanges. 
	 * The type of update is decided by the value of stamp. It informs the 
	 * variable of a change if it occurred. 
	 * @param storeLevel : Level of the store at which the update occurs
	 * @param S : Variable for which this domain is used
	 * @param el : Elements of S whose ProbabilityRanges are to be updated
	 * @param pRanges : ProbabilityRanges to which domain is updated
	 */

/* After changes in SopXrelS this method is never used...

	public void setElement(int storeLevel, StochasticVar S, int[] el, ProbabilityRange[] pRanges){
		
		//TO_DO, RADEK
		// set functions are used for setting (initial value setting) not for changes later in search
		// in functions are used for changes, 
		// therefore this set function should not look at the stamps to decide if overwrite, it 
		// should always overwrite and maybe issue warning if used during search. 
	        // KRZYSZTOF
	        // IT HAS BEEN USED IN SEARCH IN CONSTRAINT SopXrelS !!!
		assert (el.length == pRanges.length);
		
		if (eq(el, pRanges))
			return;

		if (stamp == storeLevel) {
			
			for (int i=0; i < el.length; i++) 				
				ProbRanges[i].set(pRanges[i]);
		}
		
		else{
			
			assert stamp < storeLevel;
			
			DiscreteStochasticDomain result = cloneLight();
			
			for (int i=0; i < el.length; i++) 				
				result.ProbRanges[i].set(pRanges[i]);
			
			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			S.domain = result;
		}
		
		if (S.dom().singleton()) {
			S.domainHasChanged(StochasticDomain.GROUND);
			return;
		} 
		else {
			S.domainHasChanged(StochasticDomain.BOUND);
			return;
		}	
	}
*/

	/**
	 * This method updates the domain such that the specified element has 
	 * ProbabilityRange equal to the specified ProbabilityRange. 
	 * The type of update is decided by the value of stamp. It informs the 
	 * variable of a change if it occurred. 
	 * @param storeLevel : Level of the store at which the update occurs
	 * @param S : Variable for which this domain is used
	 * @param el : Element of S whose ProbabilityRange is to be updated
	 * @param r : ProbabilityRange to which domain is updated
	 */
	public void setElement (int storeLevel, StochasticVar S, int el, ProbabilityRange r) {
		
		if (eqElement(el, r))
			return;
		
		if (stamp == storeLevel) {
			
			int index = Arrays.binarySearch(S.dom().values, el);
			
			if (index < 0)
				throw failException;
			else 
				ProbRanges[index].set(r);
		}
		
		else{
			
			assert stamp < storeLevel;
			
			DiscreteStochasticDomain result = cloneLight();
			int index = Arrays.binarySearch(S.dom().values, el);	
			
			if (index < 0)
				throw failException;
			else
				result.ProbRanges[index].set(r);
			
			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			S.domain = result;
		}
		
		if (S.dom().singleton()) {
			S.domainHasChanged(StochasticDomain.GROUND);
			return;
		} 
		else {
			S.domainHasChanged(StochasticDomain.BOUND);
			return;
		}
	}
	
	@Override
	public String checkInvariants() {
		
		if (ProbRanges.length != getSize())
			return "Number of values and Number of Probability Values do not match";
			
		return null;
	}
}