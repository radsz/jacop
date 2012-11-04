package org.jacop.stochastic.core;

import org.jacop.core.Domain;

/**
 * Defines a StochasticDomain and related operations on it.
 */

public abstract class StochasticDomain extends Domain {

	/**
	 * The minimum possible element in the domain.
	 */
	public static final int MinInt = -10000000;
	
	/**
	 * The maximum possible element in the domain.
	 */
	public static final int MaxInt = 10000000;	
	
	/**
	 * The constant for GROUND event. It has to be smaller 
	 * than the constant for events BOUND and ANY.
	 */
	public final static int GROUND = 0;

	/**
	 * The constant for BOUND event. It has to be smaller 
	 * than the constant for event ANY.
	 */
	public final static int BOUND = 1;

	/**
	 * The constant for ANY event.
	 */
	public final static int ANY = 2;

	// TODO, RADEK, What events make sense for Stochastic variable? 
	// ANY - yes
	// GROUND - maybe
	// BOUND - what would that mean? useful?
	/**
	 * It specifies for each event what other events are subsumed by this
	 * event.  
	 */
	public final static int[][] eventsInclusion = { {GROUND, BOUND, ANY}, // GROUND event 
											 		{BOUND, ANY}, // BOUND event 
											 		{ANY} }; // ANY event
	
	/**
	 * This method helps to specify what events should be executed if a given
	 * event occurs.
	 * @param pruningEvent : The pruning event for which we want to know what
	 * events it encompasses
	 * @return an array specifying what events should be included given this
	 *  event
	 */
	public int[] getEventsInclusion(int pruningEvent) {
		
		return eventsInclusion[pruningEvent];
	}
	
	/**
	 * Unique identifier for a discrete stochastic domain.
	 */
	public static final int DiscreteStochasticDomainID = 0;
	
	/**
	 * An empty stochastic domain. 
	 */
    /*   This method is never used and it is not a good style
    that abstract method uses one of its implementations, I think

	public static final StochasticDomain emptyStocIntDomain = 
									new DiscreteStochasticDomain();
	  */

	public abstract int domainID();
	
}
