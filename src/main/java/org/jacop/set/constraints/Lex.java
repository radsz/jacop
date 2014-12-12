/**
 *  Lex.java 
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

package org.jacop.set.constraints;

import java.util.ArrayList;

import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates a lex constraint on a list of set variables. Each consecutive pair of
 * set variables is being constrained to be lexicographically ordered.
 * 
 * For example, 
 * {} <lex {1}
 * {1, 2} <lex {1, 2, 3}
 * {1, 3} <lex {2}
 * {1} < {2}
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class Lex extends Constraint {

	static int idNumber = 1;

	/**
	 * It specifies a list on which element a lex relationship holds for every 
	 * two consecutive variables.
	 */
	public SetVar a;
	
	/**
	 * It specifies a list on which element a lex relationship holds for every 
	 * two consecutive variables.
	 */
	public SetVar b;

	/**
	 * It specifies if the relation is strict or not.
	 */
	public boolean strict = true;
	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"a", "b"};

	protected int inSupport;
	protected int inclusionLevel = -1;
	protected TimeStamp<IntDomain> inDifference;
	
	protected int smallerElSupport;	
	protected int smallerElLevel = -1;
	protected TimeStamp<IntDomain> smallerDifference;
	
	/**
	 * It constructs an Lexical ordering constraint to restrict the domain of the variables a and b.
	 * It is strict by default.
	 * 
	 * @param a variable that is restricted to be less than b with lexical order.
	 * @param b variable that is restricted to be greater than a with lexical order.
	 */
	public Lex(SetVar a, SetVar b) {

		assert (a != null) : "Variable a is null";
		assert (b != null) : "Variable b is null";

		numberId = idNumber++;
		numberArgs = 2;

		this.a = a;
		this.b = b;

	}

	/**
	 * It constructs an Lexical ordering constraint to restrict the domain of the variables a and b.
	 * 
	 * @param a variable that is restricted to be less than b with lexical order.
	 * @param b variable that is restricted to be greater than a with lexical order.
	 * @param strict specifies if the lex relation is strict. 
	 */
	public Lex(SetVar a, SetVar b, boolean strict) {
		
		this(a, b);
		this.strict = strict;
		
	}


	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(2);

		variables.add(a);
		variables.add(b);

		return variables;
	}

	@Override
	public void consistency(Store store) {

	    /*
		StringBuffer before = new StringBuffer( toString() );

		System.out.println("Lex<<" + before.toString() );
		// Lex<<Lex(list[0]={{ 1 }}, list[1]::{{{ 2 }}..{ 0 2 }}[card={1..2}])
		
		if (a.domain.glb().eq(new IntervalDomain(1, 1)) 
			&& b.domain.lub().eq(new IntervalDomain(0, 1)) 
			&& a.domain.lub().eq(new IntervalDomain(0, 1))
			&& b.domain.glb().eq(new IntervalDomain(1, 1)) )
				System.out.println("bug.");

		try {
		*/
		
		if (strict) {
			
			if (b.domain.lub().isEmpty())
				throw Store.failException;

		}

		if (a.domain.lub().isEmpty())
			return;		

		// Remove all elements from b.lub/b.glb which are smaller than a.lub.min().
		if (a.domain.card().min() > 0)
			b.domain.inLUB(store.level, b, new IntervalDomain(a.domain.lub().min(), Integer.MAX_VALUE));		

		if (strict && a.domain.card().singleton(1) && b.domain.card().singleton(1))
			b.domain.inLUB(store.level, b, new IntervalDomain(a.domain.lub().min() + 1, Integer.MAX_VALUE));				
		
		if (a.domain.glb().isEmpty()) {

			if (b.domain.glb().isEmpty()) {
				// a.glb = {}
				// b.glb = {}

				int minA = a.domain.lub().min();
				int maxB = b.domain.lub().max();
				
				if (strict &&  minA >= maxB || minA > maxB) 
					a.domain.inLUB(store.level, a, IntDomain.emptyIntDomain);
				
				return;
				
			}
			else {
				// a.glb = {}
				// b.glb != {}

				ValueEnumeration enumerGLBofB = b.domain.glb().valueEnumeration();
				ValueEnumeration enumerLUBofA = a.domain.lub().valueEnumeration();

				int nextElinGLBofB = enumerGLBofB.nextElement();
				int nextElinLUBofA = enumerLUBofA.nextElement();

				int lastElinLUBofA = Integer.MIN_VALUE;
				
				while (true) {
				
					// if a.lub.next < a.glb.next 
					if (nextElinLUBofA < nextElinGLBofB) {
						// A can be made also smaller for non-empty set.
						return;
					}

					// if a.lub.next == b.glb.next then continue. 
					if (nextElinLUBofA == nextElinGLBofB) {
						lastElinLUBofA = nextElinLUBofA;
						
						if (!enumerGLBofB.hasMoreElements()) 
							if (enumerLUBofA.hasMoreElements()) {
								nextElinLUBofA = enumerLUBofA.nextElement();
								if ( (strict && nextElinLUBofA < b.domain.lub().max()) ||
									 (!strict && nextElinLUBofA <= b.domain.lub().max())) {
									// an element can be added to a to make it lex smaller
									// if no element is added is also lex smaller. 
									return;
								}
								else {
									// lex can be achieved either by making it empty or not adding any elements above lastElinLUBofA.
									a.domain.inLUB(store.level, a, new IntervalDomain(Integer.MIN_VALUE, lastElinLUBofA));
									return;
								}
							}
						
						if (!enumerLUBofA.hasMoreElements())
							return;
						
						nextElinGLBofB = enumerGLBofB.nextElement();
						nextElinLUBofA = enumerLUBofA.nextElement();
						continue;
					}

					// if b.glb <lex a.lub then 
					if (nextElinGLBofB < nextElinLUBofA) {

						if (nextElinLUBofA == a.domain.lub().min()) {

							// already the first element of a.lub is larger then the smallest element of b.
							// a must be an empty set. 
							a.domain.inLUB(store.level, a, IntDomain.emptyIntDomain);
							return;

						} else {

							// all elements in a until lastElinLUBofA are allowed. 
							a.domain.inLUB(store.level, a, new IntervalDomain(Integer.MIN_VALUE, lastElinLUBofA));
							return;
						}

					}
					
				}

			}

		}
		else {
			
			if (b.domain.glb().isEmpty()) {
				// a.glb != {}
				// b.glb = {}
				
				// Does not handle yet, {0}..{0..1} <lex {}..{0..1}. TODO
				
				if (strict && a.domain.glb().max() == a.domain.lub().max() && a.domain.card().min() == 1 && a.domain.card().max() == 2 
					&& b.domain.lub().max() == a.domain.glb().max() && b.domain.card().max() == 2) {
					// Special case - {y} .. {x, y} <lex {} .. {x, y}
					// exclude x from b.lub.
					if (b.domain.lub().min() == a.domain.lub().min() )
						b.domain.inLUBComplement(store.level, b, b.domain.lub().min());
					// force x into a.glb
					a.domain.inGLB(store.level, a, a.domain.lub().min());
				}
					
					
				if (b.domain.card().min() == 0)
					b.domain.inCardinality(store.level, b, 1, Integer.MAX_VALUE);
				
			}
			else {
				// a.glb != {}
				// b.glb != {}

				// Traverse a.glb, a.lub, b.glb
				// count how many smaller elements (noSmaller) given current value can be added from a.lub to a.glb.  
				int noSmaller = 0;
				
				ValueEnumeration enumerGLBofA = a.domain.glb().valueEnumeration();
				ValueEnumeration enumerGLBofB = b.domain.glb().valueEnumeration();
				ValueEnumeration enumerLUBofA = a.domain.lub().valueEnumeration();

				int nextElinGLBofA = enumerGLBofA.nextElement();
				int nextElinGLBofB = enumerGLBofB.nextElement();
				int nextElinLUBofA = enumerLUBofA.nextElement();

				int previousElinLUBofA = Integer.MIN_VALUE;
				
				while (true) {

				// if a.glb.next <lex b.glb.next then exit. 
				if (nextElinGLBofA < nextElinGLBofB) {

					// check.
					if (strict && b.domain.card().min() + 1 == b.domain.card().max()
						&& a.domain.card().max() == 2
						&& a.domain.card().min() == b.domain.card().max()
						&& a.domain.glb().eq(b.domain.lub()))
						b.domain.inLUBComplement(store.level, b, nextElinGLBofA);
						
					return;
				
				}
				// if a.lub.next < a.glb.next && a.lub.next < b.glb.next then noSmaller++;
				if (nextElinLUBofA < nextElinGLBofA && nextElinLUBofA < nextElinGLBofB) {
					previousElinLUBofA = nextElinLUBofA;
					noSmaller++;
					// if noSmaller = 2 then two ways of fixing and so can exit. 
					if (noSmaller == 2)
						return;
					nextElinLUBofA = enumerLUBofA.nextElement();
					continue;
				}

				// if a.glb.next == b.glb.next then continue. 
				if (nextElinGLBofA == nextElinGLBofB) {
					
					if (!enumerGLBofA.hasMoreElements()) {
						if (noSmaller == 1) {
							// if b.lub.max == nextElinGLBofA
							if (strict && b.domain.lub().max() == nextElinGLBofA) {
								// Only one way of enforcing <lex relation.
								a.domain.inGLB(store.level, a, previousElinLUBofA);
							}
							return;
						}
						else {
							
							// noSmaller == 0.
							if (strict && nextElinGLBofB == b.domain.lub().previousValue( b.domain.lub().max() ))
								// only one element left to add to b.lub() to satisfy a <lex b
								b.domain.inGLB(store.level, b, b.domain.lub().max());
								
							if (strict && nextElinGLBofA == a.domain.lub().previousValue( a.domain.lub().max() )
								&& a.domain.lub().max() >= b.domain.lub().max() )
								// only one element possible to add to a, and this element is larger or equal to maximum element in b.lub then remove it.
								a.domain.inLUBComplement(store.level, a, a.domain.lub().max());
									
							if (strict && nextElinGLBofA == a.domain.lub().max() && nextElinGLBofB == b.domain.lub().max() )
								// if strict and  
								// a has no more elements in aLUB to be added and
								// b has no more elements in bLUB to be added 
								// then fail. 
								throw Store.failException;
							
							// TODO. 
							// a.glb exhausted, possibly there are some elements in a.lub that must be removed because 
							// adding them will make a !<lex b. 
							
							return;
						}
					}
					
					if (!enumerGLBofB.hasMoreElements()) {
					
						if (noSmaller == 0) {
							
							nextElinLUBofA = enumerLUBofA.nextElement();

							// bGLB exhausted, aGLB not exhausted.
							// b can not use elements between [nextElinGLBofA..nextElinLUBofA]
							if (nextElinGLBofA + 1 <= nextElinLUBofA - 1)
									b.domain.inLUB(store.level, b, new IntervalDomain(nextElinGLBofA + 1, nextElinLUBofA - 1).complement() );
									
							// all elements equal up to now in aGLB and bGLB, but bLUB has no sufficiently large element 
							// (greater than nextElinLUBofA  
							if ( (strict && nextElinLUBofA >= b.domain.lub().max()) ||
									( nextElinLUBofA > b.domain.lub().max() ) ) {
								// not possible to add any more elements to b.glb. 
								throw Store.failException;
							}

							if (strict) {
								// there is at least one element in bLUB which can be added to bGLB to satisfy a <lex b.
								int previous = b.domain.lub().previousValue( b.domain.lub().max() );
								// only one element left in B to make a <lex b true.
								if (previous == nextElinGLBofB)
									b.domain.inGLB(store.level, b, b.domain.lub().max());
							}
							
							return;
						}
						else {
							// noSmaller == 1, one way of fixing lex. 

							nextElinLUBofA = enumerLUBofA.nextElement();

							if ( (b.domain.lub().max() <= nextElinLUBofA && strict) ||
								 (b.domain.lub().max() < nextElinLUBofA && !strict)) {

								// Only one way of enforcing <lex relation.
								a.domain.inGLB(store.level, a, previousElinLUBofA);

							}
							
							return;
						}

					}
					
					nextElinGLBofA = enumerGLBofA.nextElement();
					nextElinGLBofB = enumerGLBofB.nextElement();
					nextElinLUBofA = enumerLUBofA.nextElement();
					continue;
				}

				// if b.glb <lex a.glb then 
				if (nextElinGLBofB < nextElinGLBofA) {
					
					if (noSmaller == 0) {
						// if noSmaller = 0, but b.glb.next == a.lub.next then fix it and continue.
						if (nextElinLUBofA == nextElinGLBofB) {
							a.domain.inGLB(store.level, a, nextElinGLBofB);
							// TODO, check if the enumeration is updated as assumed.
							enumerGLBofA.domainHasChanged();

							// BEGIN BUGGY most likely 
							if (!enumerGLBofB.hasMoreElements()) {

								nextElinLUBofA = enumerLUBofA.nextElement();

								if ( ( strict && nextElinLUBofA >= b.domain.lub().max() )
									|| nextElinLUBofA > b.domain.lub().max() )
									throw Store.failException;
								
								// "cheating", assuming the worst case for pruning, maximum element added to bGLB.
								nextElinGLBofB = b.domain.lub().max();
								
							}
							else {
								nextElinGLBofB = enumerGLBofB.nextElement();
								nextElinLUBofA = enumerLUBofA.nextElement();
							}
							
							continue;
							// END BUGGY
							
						}
						else
							// if noSmaller = 0 and could not fix above then fail. 
							throw Store.failException;
					}
					
					if (noSmaller == 1) {
						
						if (nextElinLUBofA == nextElinGLBofB) {

							if (!enumerGLBofB.hasMoreElements()) {

								// TODO
								// if there is no element which can be added to B to find 2nd way of making a <lex b
								// then enforce the first way. 
								// 2nd way == true, if and only if next(enumerLUBofA) < b.domain.lub.max() (for strict case, nonstrict uses <= ). 
								return;
							}

							if (!enumerLUBofA.hasMoreElements()) {
								
								// Cannot happen as lubOfA still has an element nextElinGLBofA.
								
							}

							nextElinGLBofB = enumerGLBofB.nextElement();
							nextElinLUBofA = enumerLUBofA.nextElement();

							while (true) {

								if (nextElinLUBofA < nextElinGLBofB) {
									// there exist a second way of fixing it.
									return;
								}
								else 
									if (nextElinGLBofB < nextElinLUBofA) {
										// Only way one of fixing it.
										a.domain.inGLB(store.level, a, previousElinLUBofA);
										return;
									}
									else {
										// nextElinLUBofA == nextElinGLBofB, still not decided if there is a second way to fix it.
										
										if (!enumerGLBofB.hasMoreElements()) {

											// TODO
											// if there is no element which can be added to B to find 2nd way of making a <lex b
											// then enforce the first way. 
											// 2nd way == true, if and only if next(enumerLUBofA) < b.domain.lub.max() (for strict case, nonstrict uses <= ). 
											return;
										}

										if (!enumerLUBofA.hasMoreElements()) {
											
											// Cannot happen as lubOfA still has an element nextElinGLBofA.
											
										}

										nextElinGLBofB = enumerGLBofB.nextElement();
										nextElinLUBofA = enumerLUBofA.nextElement();
										
									}
										
							}
							
						}
						else {
							// if noSmaller = 1 then fix it (put right element in a.glb) and exit. 
							// fixable by adding previously smaller element.
							a.domain.inGLB(store.level, a, previousElinLUBofA);
							return;
						}
						
					}
				}
				
				}
					
			}
		
		}

		/*
		}
		catch(FailException ex) {

			System.out.println("BeforeFail " + before.toString() );
			System.out.println("AfterFail  " + toString() );
			throw ex;
		}
		finally {

//			if (!before.toString().equals(toString())) {
				System.out.println("Lex<<" + before.toString() );
				System.out.println("Lex>>" + toString() );
//			}

		}
		*/
		
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return SetDomain.ANY;		
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

		store.registerRemoveLevelListener(this);
		smallerDifference = new TimeStamp<IntDomain>(store, a.domain.lub().subtract(b.domain.glb()));
		inDifference = new TimeStamp<IntDomain>(store, b.domain.lub().subtract( a.domain.glb() ));
		
		a.putModelConstraint(this, getConsistencyPruningEvent(a));
		b.putModelConstraint(this, getConsistencyPruningEvent(b));

		assert (!a.domain.lub().contains(Integer.MIN_VALUE)) : "Lex constraint does not allow Integer.MIN_VALUE in the domain";
		assert (!b.domain.lub().contains(Integer.MIN_VALUE)) : "Lex constraint does not allow Integer.MIN_VALUE in the domain";
		
		inSupport = Integer.MIN_VALUE;
		
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeLevel(int level) {
		if (inclusionLevel == level)
			inclusionLevel = -1;
		if (smallerElLevel == level)
			smallerElLevel = -1;
	}

	@Override
	public void removeConstraint() {

		a.removeConstraint(this);
		b.removeConstraint(this);

	}

	@Override
	public boolean satisfied() {

		// FIXME, 
		// create function based on the counter of grounded variables. 

		return false;
	}

	@Override
	public String toString() {

		StringBuffer result = new StringBuffer();
		result.append("Lex(");
		result.append(a).append(", ").append(b);
		result.append(")");
		return result.toString();
		
	}

	@Override
	public void increaseWeight() {

		if (increaseWeight) {
			a.weight++;
			b.weight++;
		}

	}	

}
