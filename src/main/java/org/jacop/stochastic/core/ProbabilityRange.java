package org.jacop.stochastic.core;

import org.jacop.core.Store;
import java.text.DecimalFormat;

/**
 * Defines a ProbabilityRange and related operations on it.
 */

public class ProbabilityRange {

	/**
	 * Minimum value of this ProbabilityRange object.
	 */
	public double min;
	
	/**
	 * Maximum value of this ProbabilityRange object.
	 */
	public double max;
	
	/**
	 * Minimum possible value of a ProbabilityRange object.
	 */
	public static final double MinLimit = 0;
	
	/**
	 * Maximum possible value of a probabilityRange object.
	 */
	public static final double MaxLimit = 1;	
	
	/**
	 * Interval of precision when comparing 2 floats.
	 */
        public static final double epsilon = (float)1.0E-11; //0.0000001;
	
	/**
	 * This constructor creates an instance of ProbailityRange with default
	 * values equal to the limits.
	 */
	public ProbabilityRange() {
		
		min = MinLimit;
		max = MaxLimit;
	}
	
	/** This constructor creates a new instance of ProbabiltyRange. It requires
	 *  min to be smaller than or equal to max. If min or max are outside the 
	 *  limits of ProbabilityRange, they are set to the nearest limit.
	 * @param min : The left bound of the ProbabilityRange (inclusive)  
	 * @param max : The right bound of the ProbabilityRange (inclusive)
	 */
	public ProbabilityRange(double min, double max) {
		
		// assert (min <= max) : "min is greater than max !";
		
		min = (min <= MaxLimit) ? min : MaxLimit;
		min = (min >= MinLimit) ? min : MinLimit;
		
		max = (max <= MaxLimit) ? max : MaxLimit;
		max = (max >= MinLimit) ? max : MinLimit;
		
		this.min = round(min);
		this.max = round(max);
	}
	
	/** This constructor creates a new instance of a singleton ProbabiltyRange.
	 * @param val : value of the singleton ProbabiltyRange  
	 */
	public ProbabilityRange(double val) {
				
		val = (val <= MaxLimit) ? val : MaxLimit;
		val = (val >= MinLimit) ? val : MinLimit;
		
		this.min = round(val);
		this.max = round(val);
	}

	/**
	 * This method clears the ProbabilityRange instance and sets min and 
	 * max equal to 0.
	 */
	public void clear() {
		
		min = 0;
		max = 0;
	}

	/**
	 * This method checks if the ProbabilityRange instance is empty.
	 * @return true if the instance is empty, false otherwise
	 */
	public boolean isEmpty() {
		
		return (singleton() && max == 0);
	}

	/**
	 * This method checks if the ProbabilityRange instance takes only 
	 * a single value.
	 * @return true if the instance is a singleton, false otherwise
	 */
	public boolean singleton() {
		
		return (Math.abs( max - min ) < epsilon);
	}

    /**
     * This method compares two ProbabilityRange instances.
     * @return true if min is equal max, false otherwise
     */
    public boolean eq() {

        return (max - min) < epsilon;
    }

	/**
	 * This method compares two ProbabilityRange instances.
	 * @param r : ProbabilityRange instance to be compared
	 * @return true if the two instances are equal, false otherwise
	 */
	public boolean eq(ProbabilityRange r) {
		
		return eq(r.min, r.max);
	}

	/**
	 * This method checks if the ProbabilityRange is equal to the range
	 * specified as doubles.
	 * @param minP : Minimum value
	 * @param maxP : Maximum value
	 * @return true if the ranges match, false otherwise
	 */
	public boolean eq(double minP, double maxP){
		
		return (Math.abs(minP - min) < epsilon && 
				Math.abs(maxP - max) < epsilon);
	}
	
	/**
	 * This method checks if the ProbabilityRange is equal to the range
	 * specified as ints with a given resolution.
	 * @param minP : Minimum value
	 * @param maxP : Maximum value
	 * @param res : Resolution
	 * @return true if the ranges match, false otherwise
	 */
	public boolean eq(int minP, int maxP, int res){
		
		return (((int)min*res == minP)&&
				((int)min*res == minP));
	}

	/**
	 * This method sets ProbabilityRange instance attributes with
	 * those of the specified ProbabilityRange.
	 * @param r : Specified ProbabilityRange
	 */
	public void set(ProbabilityRange r) {

	    min = round(r.min);
	    max = round(r.max);
	}
	
	/**
	 * This method computes the union of this ProbabilityRange instance with
	 * the specified ProbabilityRange.
	 * @param r : Specified ProbabilityRange
	 */
	public void union(ProbabilityRange r) {

            min = (min <= r.min) ? min : r.min;

            max = (max >= r.max) ? max : r.max;

	    min = round(min);
	    max = round(max);
    }

	/**
	 * This method computes the sum of this ProbabilityRange instance with
	 * the specified ProbabilityRange.
	 * @param r : Specified ProbabilityRange
	 * returns resulting ProbabilityRange
	 */
	public void add(ProbabilityRange r) {
		
	    min = ((min + r.min)<= MaxLimit) ? (min + r.min) : MaxLimit; 
	    max = ((max + r.max)<= MaxLimit) ? (max + r.max) : MaxLimit; 

	    min = round(min);
	    max = round(max);
	}
	
	/** 
	 * This method updates this ProbabilityRange to have values only within the
	 * specified interval min..max.
	 * @param min : Minimum value
	 * @param max : Maximum value
	 */
    public void in(double min, double max) {
		
	if (eq(min, max))
	    return;

        if (this.max < min || this.min > max){
            throw Store.failException;
        }
			
        if (min <= this.min && max >= this.max)
            return;
		
        if (this.min < min )
            this.min = round(min);
		
        if (this.max > max)
            this.max = round(max);
    }

    public void inWithoutFail(ProbabilityRange r) {

        inWithoutFail(r.min, r.max);
    }

    public void inWithoutFail(double min, double max) {

	if (eq(min, max))
	    return;

        if (this.max < min || this.min > max){
            this.clear();
            return;
        }

        if (min <= this.min && max >= this.max)
            return;

        if (this.min < min )
            this.min = round(min);

        if (this.max > max)
            this.max = round(max);
    }

	/**
	 * This method updates this ProbabilityRange to have values only within the
	 * specified interval min..max.
	 * @param min : Minimum value
	 * @param max : Maximum value
	 * @param res : Resolution
	 */
	public void in(int min, int max, int res){
		
		double minP = min/res;
		double maxP = max/res;
	
		in(minP, maxP);
	}
	
	/**
	 * This method updates this ProbabilityRange to have values only within the
	 * specified ProbabilityRange. 
	 * @param r : Specified ProbabilityRange
	 */
	public void in(ProbabilityRange r) {
		
		in(r.min, r.max);
	}
	
	/**
	 * This method checks if a given value belongs to this ProbabilityRange
	 * instance for a specified resolution.
	 * @param x : Value
	 * @param res : Resolution
	 * @return true, if it belongs to the range
	 */
	public boolean belongs(int x, int res) {
		
		return (x >= (int)(min*res)) &&
			   (x <= (int)(max*res));
	}
	
	/**
	 * This method checks if this ProbabilityRange intersects with the 
	 * specified interval min..max for a given resolution.
	 * @param min : Minimum value
	 * @param max : Maximum value
	 * @param res : Resolution
	 * @return true, if there is an intersection
	 */
	public boolean intersects(int min, int max, int res) {
		
		if ((int)(this.max*res) < min || (int)(this.min*res) > max)
			return false;
			
		return true;	
	}
	
	/**
	 * This method gives a string representation of the ProbabilityRange 
	 * instance.
	 * @return String representation of the ProbabilityRange instance
	 */
	@Override
	public String toString() {

	    if ( (max - min) < epsilon )
		return formatProbability(min);
	    else if (min < max)
		return "{" + formatProbability(min) + ".." + formatProbability(max) + "}";
	    else
		return "{}";

	}

    public String formatProbability(double p) {

	DecimalFormat df1 = new DecimalFormat("0.####");
	DecimalFormat df2 = new DecimalFormat("0.####E0");

	if (p == 0)
	    return ""+0;
	else if (p >= 0.0001)
	    return df1.format(p);
	else
	    return df2.format(p); 
    }

	/**
	 * This method checks if all the invariants of the ProbabilityRange instance
	 * are satisfied.
	 * @return Unsatisfied invariant, if any
	 */
	public String checkInvariants() {

		if (this.min > this.max)
			return "Min value is larger than max value ";
		if (this.min < MinLimit || this.min > MaxLimit)
			return "Min value is not in the range of 0 and 1";
		if (this.max < MinLimit || this.max > MaxLimit)
			return "Max value is not in the range of 0 and 1";
		
		//Fine, all invariants hold.
		return null;
	}

    private double round(double x) {

	// double result = Math.round(x*1000000000)/1000000000.0;
	// Return result;

	return x;

	// return Double.valueOf(probabilityFormat.format(x));

    }
}

