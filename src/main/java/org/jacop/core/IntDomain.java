/**
 *  IntDomain.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.core;

import java.util.Random;

/**
 * Defines an integer domain and related operations on it.
 * 
 * IntDomain implementations can not assume that arguments to 
 * any function can not be empty domains. 

 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 3.1
 */

public abstract class IntDomain extends Domain {

	// FIXME, implement as much as possible in general (inefficient) manner, but
	// it will allow new IntDomain to quickly be employed within a solver.	

	/**
	 * It specifies the minimum element in the domain.
	 */
	public static final int MinInt = -50000000;

	/**
	 * It specifies the maximum element in the domain.
	 */
	public static final int MaxInt = 50000000;	

	/**
	 * It specifies the constant for GROUND event. It has to be smaller 
	 * than the constant for events BOUND and ANY.
	 */
	public final static int GROUND = 0;

	/**
	 * It specifies the constant for BOUND event. It has to be smaller 
	 * than the constant for event ANY.
	 */
	public final static int BOUND = 1;

	/**
	 * It specifies the constant for ANY event.
	 */
	public final static int ANY = 2;


	/**
	 * It specifies for each event what other events are subsumed by this
	 * event. Possibly implement this by bit flags in int. 
	 */
	public final static int[][] eventsInclusion = { {GROUND, BOUND, ANY}, // GROUND event 
		{BOUND, ANY}, // BOUND event 
		{ANY} }; // ANY event

	/**
	 * It helps to specify what events should be executed if a given event occurs.
	 * @param pruningEvent the pruning event for which we want to know what events it encompasses.
	 * @return an array specifying what events should be included given this event.
	 */
	public int[] getEventsInclusion(int pruningEvent) {
		return eventsInclusion[pruningEvent];
	}

	/**
	 * Unique identifier for an interval domain type.
	 */

	public static final int IntervalDomainID = 0;

	/**
	 * Unique identifier for a bound domain type.
	 */

	public static final int BoundDomainID = 1;

	/**
	 * Unique identifier for a small dense domain type.
	 */

	public static final int SmallDenseDomainID = 2;

	/**
	 * It specifies an empty integer domain. 
	 */
	public static final IntDomain emptyIntDomain = new IntervalDomain(0);

	/**
	 * It adds interval of values to the domain.
	 * @param i Interval which needs to be added to the domain.
	 */

	public void unionAdapt(Interval i) {
		unionAdapt(i.min, i.max);
	}

	/**
	 * It adds values as specified by the parameter to the domain.
	 * @param domain Domain which needs to be added to the domain.
	 */

	public void addDom(IntDomain domain) {

		if (!domain.isSparseRepresentation()) {
			IntervalEnumeration enumer = domain.intervalEnumeration();
			while (enumer.hasMoreElements())
				unionAdapt(enumer.nextElement());
		}
		else {
			ValueEnumeration enumer = domain.valueEnumeration();
			while (enumer.hasMoreElements())
				unionAdapt(enumer.nextElement());
		}

	};

	/**
	 * It adds all values between min and max to the domain.
	 * @param min the left bound of the interval being added.
	 * @param max the right bound of the interval being added.
	 */

	public abstract void unionAdapt(int min, int max);

	/**
	 * It adds a values to the domain.
	 * @param value value being added to the domain.
	 */

	public void unionAdapt(int value) {
		unionAdapt(value, value);
	}

	/**
	 * Checks if two domains intersect.
	 * @param domain the domain for which intersection is checked.
	 * @return true if domains are intersecting.
	 */

	public boolean isIntersecting(IntDomain domain) {

		if (!domain.isSparseRepresentation()) {
			IntervalEnumeration enumer = domain.intervalEnumeration();
			while (enumer.hasMoreElements()) {
				Interval next = enumer.nextElement();
				if (isIntersecting(next.min, next.max))
					return true;
			}
		}
		else {

			ValueEnumeration enumer = domain.valueEnumeration();
			while (enumer.hasMoreElements())
				if (contains(enumer.nextElement()))
					return true;
		}

		return false;
	}

	/**
	 * It checks if interval min..max intersects with current domain.
	 * @param min the left bound of the interval.
	 * @param max the right bound of the interval.
	 * @return true if domain intersects with the specified interval.
	 */

	public abstract boolean isIntersecting(int min, int max);

	/**
	 * It specifies if the current domain contains the domain given as a
	 * parameter.
	 * @param domain for which we check if it is contained in the current domain.
	 * @return true if the supplied domain is cover by this domain.
	 */

	public boolean contains(IntDomain domain) {

		if (!domain.isSparseRepresentation()) {
			IntervalEnumeration enumer = domain.intervalEnumeration();
			while (enumer.hasMoreElements()) {
				Interval next = enumer.nextElement();
				if (!contains(next.min, next.max))
					return false;
			}
		}
		else {
			ValueEnumeration enumer = domain.valueEnumeration();
			while (enumer.hasMoreElements())
				if (!contains(enumer.nextElement()))
					return false;
		}

		return true;

	}

	/**
	 * It checks if an interval min..max belongs to the domain.
	 * @param min the minimum value of the interval being checked
	 * @param max the maximum value of the interval being checked
	 * @return true if value belongs to the domain.
	 */

	public abstract boolean contains(int min, int max);

	/**
	 * It creates a complement of a domain.
	 * @return it returns the complement of this domain.
	 */

	public abstract IntDomain complement();

	/**
	 * It checks if value belongs to the domain.
	 * @param value which is checked if it exists in the domain.
	 * @return true if value belongs to the domain.
	 */

	public boolean contains(int value) {
		return contains(value, value);
	}

	/**
	 * It gives next value in the domain from the given one (lexigraphical
	 * ordering). If no value can be found then returns the same value.
	 * @param value it specifies the value after which a next value has to be found.
	 * @return next value after the specified one which belong to this domain.
	 */

	public abstract int nextValue(int value);

	/**
	 * It gives previous value in the domain from the given one (lexigraphical
	 * ordering). If no value can be found then returns the same value.
	 * @param value before which a value is seeked for.
	 * @return it returns the value before the one specified as a parameter.
	 */

	public abstract int previousValue(int value);

	/**
	 * It returns value enumeration of the domain values.
	 * @return valueEnumeration which can be used to enumerate one by one value from this domain.
	 */

	public abstract ValueEnumeration valueEnumeration();

	/**
	 * It returns interval enumeration of the domain values.
	 * @return intervalEnumeration which can be used to enumerate intervals in this domain.
	 */

	public abstract IntervalEnumeration intervalEnumeration();

	/**
	 * It returns the size of the domain.
	 * @return number of elements in this domain.
	 */

	public abstract int getSize();

	/**
	 * It intersects current domain with the one given as a parameter.
	 * @param dom domain with which the intersection needs to be computed.
	 * @return the intersection between supplied domain and this domain.
	 */

	public abstract IntDomain intersect(IntDomain dom);

	/**
	 * In intersects current domain with the interval min..max.
	 * @param min the left bound of the interval (inclusive)
	 * @param max the right bound of the interval (inclusive)
	 * @return the intersection between the specified interval and this domain.
	 */

	public abstract IntDomain intersect(int min, int max);

	/**
	 * It intersects with the domain which is a complement of value. 
	 * @param value the value for which the complement is computed
	 * @return the domain which does not contain specified value.
	 */

	public IntDomain subtract(int value) {
		return subtract(value, value);
	}

	/**
	 * It removes value from the domain. It adapts current (this) domain. 
	 * @param value the value for which the complement is computed
	 */

	public abstract void subtractAdapt(int value);

	/**
	 * It removes all values between min and max to the domain.
	 * @param min the left bound of the interval being removed.
	 * @param max the right bound of the interval being removed.
	 */

	public abstract void subtractAdapt(int min, int max);



	/**
	 * It returns the maximum value in a domain.
	 * @return the largest value present in the domain.
	 */

	public abstract int max();

	/**
	 * It returns the minimum value in a domain.
	 * @return the smallest value present in the domain.
	 */
	public abstract int min();

	/**
	 * It sets the domain to the specified domain.
	 * @param domain the domain from which this domain takes all elements.
	 */

	public abstract void setDomain(IntDomain domain);

	/**
	 * It sets this domain to contain exactly all values between min and max.
	 * @param min the left bound of the interval (inclusive).
	 * @param max the right bound of the interval (inclusive).
	 */

	public abstract void setDomain(int min, int max);

	/**
	 * It returns true if given domain has only one element equal c.
	 * @param c the value to which the only element should be equal to.
	 * @return true if the domain contains only one element c.
	 */

	public boolean singleton(int c) {
		return min() == c && getSize() == 1;
	};


	/**
	 * It subtracts domain from current domain and returns the result.
	 * @param domain the domain which is subtracted from this domain.
	 * @return the result of the subtraction.
	 */

	public IntDomain subtract(IntDomain domain) {

		if (domain.isEmpty())
			return this.cloneLight();

		if (!domain.isSparseRepresentation()) {
			IntervalEnumeration enumer = domain.intervalEnumeration();
			Interval first = enumer.nextElement();
			IntDomain result = this.subtract(first.min, first.max);
			while (enumer.hasMoreElements()) {
				Interval next = enumer.nextElement();
				result.subtractAdapt(next.min, next.max);

			}
			return result;
		}
		else {
			ValueEnumeration enumer = domain.valueEnumeration();
			int first = enumer.nextElement();
			IntDomain result = this.subtract(first);
			while (enumer.hasMoreElements()) {
				int next = enumer.nextElement();
				if (result.contains(next))
					result.subtractAdapt(next);
			}
			return result;
		}

	}

	/**
	 * It subtracts interval min..max.
	 * @param min the left bound of the interval (inclusive).
	 * @param max the right bound of the interval (inclusive).
	 * @return the result of the subtraction.
	 */

	public abstract IntDomain subtract(int min, int max);

	/**
	 * It computes union of the supplied domain with this domain.
	 * @param domain the domain for which the union is computed.
	 * @return the union of this domain with the supplied one.
	 */

	public IntDomain union(IntDomain domain) {

		if (this.isEmpty())
			return domain.cloneLight();

		IntDomain result = this.cloneLight();

		if (domain.isEmpty())
			return result;

		if (!domain.isSparseRepresentation()) {
			IntervalEnumeration enumer = domain.intervalEnumeration();
			while (enumer.hasMoreElements()) {
				Interval next = enumer.nextElement();
				result.unionAdapt(next.min, next.max);					
			}
			return result;
		}
		else {
			ValueEnumeration enumer = domain.valueEnumeration();
			while (enumer.hasMoreElements()) {
				int next = enumer.nextElement();
				result.unionAdapt(next);
			}
			return result;
		}

	}

	/**
	 * It computes union of this domain and the interval.
	 * @param min the left bound of the interval (inclusive).
	 * @param max the right bound of the interval (inclusive).
	 * @return the union of this domain and the interval.
	 */

	public IntDomain union(int min, int max) {

		IntDomain result = this.cloneLight();
		result.unionAdapt(min, max);
		return result;

	};

	/**
	 * It computes union of this domain and value. 
	 * 
	 * @param value it specifies the value which is being added.
	 * @return domain which is a union of this one and the value.
	 */

	public IntDomain union(int value) {
		return union(value, value);
	}

	/**
	 * It updates the domain according to the minimum value and stamp value. It
	 * informs the variable of a change if it occurred.
	 * @param storeLevel level of the store at which the update occurs.
	 * @param var variable for which this domain is used.
	 * @param min the minimum value to which the domain is updated.
	 */

	public void inMin(int storeLevel, Var var, int min) {

		in(storeLevel, var, min, max());

	};

	/**
	 * It updates the domain according to the maximum value and stamp value. It
	 * informs the variable of a change if it occurred.
	 * @param storeLevel level of the store at which the update occurs.
	 * @param var variable for which this domain is used.
	 * @param max the maximum value to which the domain is updated.
	 */

	public void inMax(int storeLevel, Var var, int max) {

		in(storeLevel, var, min(), max);

	};

	/**
	 * It updates the domain to have values only within the interval min..max.
	 * The type of update is decided by the value of stamp. It informs the
	 * variable of a change if it occurred.
	 * @param storeLevel level of the store at which the update occurs.
	 * @param var variable for which this domain is used.
	 * @param min the minimum value to which the domain is updated.
	 * @param max the maximum value to which the domain is updated.
	 */

	public abstract void in(int storeLevel, Var var, int min, int max);

	/**
	 * It reduces domain to a single value. 
	 * 
	 * @param level level of the store at which the update occurs.
	 * @param var variable for which this domain is used.
	 * @param value the value according to which the domain is updated.
	 */
	public void inValue(int level, IntVar var, int value) {
		in(level, var, value, value);
	}

	/**
	 * It updates the domain to have values only within the domain. The type of
	 * update is decided by the value of stamp. It informs the variable of a
	 * change if it occurred.
	 * @param storeLevel level of the store at which the update occurs.
	 * @param var variable for which this domain is used.
	 * @param domain the domain according to which the domain is updated.
	 */

	public void in(int storeLevel, Var var, IntDomain domain) {

		inShift(storeLevel, var, domain, 0);

	};

	/**
	 * It updates the domain to not contain the value complement. It informs the
	 * variable of a change if it occurred.
	 * @param storeLevel level of the store at which the update occurs.
	 * @param var variable for which this domain is used.
	 * @param complement value which is removed from the domain if it belonged to the domain.
	 */

	public void inComplement(int storeLevel, Var var, int complement) {

		inComplement(storeLevel, var, complement, complement);

	}

	/**
	 * It updates the domain so it does not contain the supplied interval. It informs
	 * the variable of a change if it occurred.
	 * @param storeLevel level of the store at which the update occurs.
	 * @param var variable for which this domain is used.
	 * @param min the left bound of the interval (inclusive).
	 * @param max the right bound of the interval (inclusive).
	 */

	public abstract void inComplement(int storeLevel, Var var, int min, int max);

	/**
	 * It returns number of intervals required to represent this domain.
	 * @return the number of intervals in the domain.
	 */
	public abstract int noIntervals();

	/**
	 * It returns required interval.
	 * @param position the position of the interval.
	 * @return the interval, or null if the required interval does not exist.
	 */
	public abstract Interval getInterval(int position);

	/**
	 * It updates the domain to contain the elements as specifed by the domain,
	 * which is shifted. E.g. {1..4} + 3 = 4..7
	 * @param storeLevel level of the store at which the update occurs.
	 * @param var variable for which this domain is used.
	 * @param domain the domain according to which the domain is updated.
	 * @param shift the shift which is used to shift the domain supplied as argument.
	 */

	public abstract void inShift(int storeLevel, Var var, IntDomain domain, int shift);

	/**
	 * It returns the left most element of the given interval.
	 * @param intervalNo the interval number.
	 * @return the left bound of the specified interval.
	 */

	public int leftElement(int intervalNo) {
		return getInterval(intervalNo).min;
	};

	/**
	 * It returns the right most element of the given interval.
	 * @param intervalNo the interval number.
	 * @return the right bound of the specified interval.
	 */

	public int rightElement(int intervalNo)  {
		return getInterval(intervalNo).max;
	};

	/**
	 * It returns the values which have been removed at current store level.
	 * @param currentStoreLevel the current store level.
	 * @return emptyDomain if domain did not change at current level, or the set of values which have been removed at current level.
	 */

	public abstract IntDomain recentDomainPruning(int currentStoreLevel);

    /**
     * It returns domain at earlier level at which the change has occurred.
     * @return previous domain
     */
    public abstract IntDomain previousDomain();

	/**
	 * It specifies if the other int domain is equal to this one. 
	 * 
	 * @param domain the domain which is compared to this domain. 
	 * 
	 * @return true if both domains contain the same elements, false otherwise.
	 */
	public boolean eq(IntDomain domain) {

		if (this.getSize() != domain.getSize())
			return false;

		// the same size.
		if (!domain.isSparseRepresentation()) {
			IntervalEnumeration enumer = domain.intervalEnumeration();
			while (enumer.hasMoreElements()) {
				Interval next = enumer.nextElement();
				if (!contains(next.min, next.max))
					return false;
			}
			return true;
		}
		else {
			ValueEnumeration enumer = domain.valueEnumeration();
			while (enumer.hasMoreElements()) {
				int next = enumer.nextElement();
				if (!contains(next))
					return false;
			}
			return true;
		}


	}

	@Override
	public void in(int level, Var var, Domain domain) {
		in(level, (IntVar)var, (IntDomain)domain);
	}	

	@Override 
	public boolean singleton(Domain value) {

		if (getSize() > 1)
			return false;

		if (isEmpty())
			return false;

		if (value.getSize() != 1)
			throw new IllegalArgumentException("An argument should be a singleton domain");

		assert (value instanceof IntDomain) : "Can not compare int domains with other types of domains.";

		IntDomain domain = (IntDomain) value;

		if (eq(domain))
			return true;
		else
			return false;

	}

	/**
	 * It returns the number of constraints
	 * @return the number of constraints attached to this domain.
	 */

	public int noConstraints() {
		return searchConstraintsToEvaluate 
				+ modelConstraintsToEvaluate[GROUND]
						+ modelConstraintsToEvaluate[BOUND]
								+ modelConstraintsToEvaluate[ANY];
	}

	public abstract IntDomain cloneLight();

	/**
	 * Returns the lexical ordering between the sets
	 * @param domain the set that should be lexically compared to this set
	 * @return -1 if s is greater than this set, 0 if s is equal to this set and else it returns 1.
	 */
	public int lex(IntDomain domain){

		ValueEnumeration thisEnumer = this.valueEnumeration();
		ValueEnumeration paramEnumer = domain.valueEnumeration();

		int i,j;

		while(thisEnumer.hasMoreElements()) {

			i = thisEnumer.nextElement();

			if( paramEnumer.hasMoreElements() ) {

				j = paramEnumer.nextElement();

				if( i < j )
					return -1;
				else if( j < i )
					return 1;
			} else
				return 1;
		}

		if(paramEnumer.hasMoreElements())
			return -1;

		return 0;

	}

	/**
	 * It returns the number of elements smaller than el.
	 * @param el the element from which counted elements must be smaller than.
	 * @return the number of elements which are smaller than the provided element el.
	 */
	public int elementsSmallerThan(int el){

		int counter = -1;

		int value = el - 1;

		while(value != el){
			value = el;
			el = previousValue(el);
			counter++;
		}

		return counter;		
	}


	/**
	 * It computes an intersection with a given domain and stores it in this domain. 
	 * 
	 * @param intersect domain with which the intersection is being computed.
	 * @return type of event which has occurred due to the operation. 
	 */
	public abstract int intersectAdapt(IntDomain intersect);

	/**
	 * It computes a union between this domain and the domain provided as a parameter. This
	 * domain is changed to reflect the result. 
	 * 
	 * @param union the domain with is used for the union operation with this domain. 
	 * @return it returns information about the pruning event which has occurred due to this operation. 
	 */
	public int unionAdapt(IntDomain union) {

		IntDomain result = union(union);

		if (result.getSize() == getSize())
			return Domain.NONE;
		else {
			setDomain(result);
			// FIXME, how to setup events for domain extending events?
			return IntDomain.ANY;
		}
	}

	/**
	 * It computes an intersection of this domain with an interval [min..max]. 
	 * It adapts this domain to the result of the intersection. 
	 * @param min the minimum value of the interval used in the intersection computation. 
	 * @param max the maximum value of the interval used in the intersection computation. 
	 * @return it returns information about the pruning event which has occurred due to this operation. 
	 */
	public abstract int intersectAdapt(int min, int max);


	/**
	 * It computes the size of the intersection between this domain and the domain 
	 * supplied as a parameter. 
	 * 
	 * @param domain the domain with which the intersection is computed.
	 * @return the size of the intersection.
	 * 
	 */
	public int sizeOfIntersection(IntDomain domain) {
		return intersect(domain).getSize();
	};

	/**
	 * It access the element at the specified position. 
	 * @param index the position of the element, indexing starts from 0. 
	 * @return the value at a given position in the domain. 
	 * 
	 */
	public abstract int getElementAt(int index);

	/**
	 * It constructs and int array containing all elements in the domain. 
	 * The array will have size equal to the number of elements in the domain.
	 * 
	 * @return the int array containing all elements in a domain.
	 */
	public int[] toIntArray() {

		int[] result = new int[getSize()];

		ValueEnumeration enumer = this.valueEnumeration();
		int i = 0;

		while(enumer.hasMoreElements())
			result[i++] = enumer.nextElement();

		return result;
	}

	/**
	 * It returns the value to which this domain is grounded. It assumes
	 * that a domain is a singleton domain. 
	 * 
	 * @return the only value remaining in the domain.
	 */
	public int value() {

		assert ( singleton() ) : "function value() called when domain is not a singleton domain.";

		return min();

	}

	private final static Random generator = new Random();

	/**
	 * It returns a random value from the domain.
	 * 
	 * @return random value. 
	 */
	public int getRandomValue() {
		return getElementAt(generator.nextInt(getSize()));
	}

	/* 
	 * Finds result interval for multiplication of {a..b} * {c..d}
	 */
	public final static IntervalDomain mulBounds(int a, int b, int c, int d) {
		
		int min = Math.min(Math.min(multiply(a,c),multiply(a,d)), Math.min(multiply(b,c),multiply(b,d)));
		int max = Math.max(Math.max(multiply(a,c),multiply(a,d)), Math.max(multiply(b,c),multiply(b,d)));
		
		return new IntervalDomain(min, max);
	}

	/* 
	 * Finds result interval for division of {a..b} / {c..d} for div and mod constraints
	 */
	public final static IntervalDomain divBounds (int a, int b, int c, int d) {

		int min=0, max=0;

		IntervalDomain result = null;

		if (a <= 0 && b >= 0 && c <= 0 && d >= 0) { // case 1
			min = IntDomain.MinInt;
			max = IntDomain.MaxInt;
			result = new IntervalDomain(min, max);
		}

		else if (c == 0 && d == 0 && (a > 0 || b < 0)) // case 2
			throw Store.failException;

		else if ( c < 0 && d > 0 && (a > 0 || b < 0)) { // case 3
			max = Math.max(Math.abs(a), Math.abs(b));
			min = -max;
			result = new IntervalDomain(min, max);	    
		}

		else if (c == 0 && d != 0 && (a > 0 || b < 0)) // case 4 a
			result = divBounds(a, b, 1, d);
		else if (c != 0 && d == 0 && (a > 0 || b < 0)) // case 4 b
			result = divBounds(a, b, c, -1);

		else { // if (c > 0 || d < 0) { // case 5
			int ac = a/c, ad = a/d, bc = b/c, bd =b/d;
			min = Math.min(Math.min(ac, ad), Math.min(bc, bd));
			max = Math.max(Math.max(ac, ad), Math.max(bc, bd));
			result = new IntervalDomain(min, max);
		}

		return result;
	}

	/* 
	 * Finds result interval for division of {a..b} / {c..d} for mul constraints
	 */
	public final static IntervalDomain divIntBounds (int a, int b, int c, int d) {
		int min=0, max=0;

		IntervalDomain result=null;

		if (a <= 0 && b >= 0 && c <= 0 && d >= 0) { // case 1
			min = IntDomain.MinInt;
			max = IntDomain.MaxInt;
			result = new IntervalDomain(min, max);
		}

		else if (c == 0 && d == 0 && (a > 0 || b < 0)) // case 2
			throw Store.failException;

		else if ( c < 0 && d > 0 && (a > 0 || b < 0)) { // case 3
			max = Math.max(Math.abs(a), Math.abs(b));
			min = -max;
			result = new IntervalDomain(min, max);	    
		}

		else if (c == 0 && d != 0 && (a > 0 || b < 0)) // case 4 a
			result = divIntBounds(a, b, 1, d);
		else if (c != 0 && d == 0 && (a > 0 || b < 0)) // case 4 b
			result = divIntBounds(a, b, c, -1);

		else { // if (c > 0 || d < 0) { // case 5
			float ac = (float)a/c, ad = (float)a/d, 
					bc = (float)b/c, bd = (float)b/d;
			float low = Math.min(Math.min(ac, ad), Math.min(bc, bd));
			float high = Math.max(Math.max(ac, ad), Math.max(bc, bd));
			min = (int)Math.round( Math.ceil( low ) );
			max = (int)Math.round( Math.floor( high ));
			if (min > max) throw Store.failException;
			result = new IntervalDomain(min, max);
		}

		return result;
	}

	public final static int multiply(int a, int b)  {

	    long m = (long)a * (long)b;
	    if (m < Integer.MIN_VALUE || m > Integer.MAX_VALUE) 
		throw new ArithmeticException("Overflow occurred from int " + a + " * " + b);  

	    return a*b;  
	}

}
