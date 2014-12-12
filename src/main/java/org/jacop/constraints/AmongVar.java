/**
 *  AmongVar.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2008 Polina Maakeva and Radoslaw Szymanek
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.LinkedHashSet;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.MutableDomain;
import org.jacop.core.MutableDomainValue;
import org.jacop.core.MutableVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
* Among constraint in its general form. It establishes the following
* relation. The given number N of X`s take values from the set
* specified by Y`s. 
* 
* This constraint significantly extends the algorithms presented in 
* the literature as it does not use the decomposition into simpler
* constraints. 
* 
* Therefore as a result, it provides stronger pruning methods without
* noticeable increase in the execution time. The large part of the 
* computation is reused across following executions of the consistency 
* function. The strength of propagation algorithm is incomporable to BC.
* 
* @author Polina Makeeva and Radoslaw Szymanek
* @version 4.2
*/

public class AmongVar extends Constraint {
	
	/**
	 * It turns out printing debugging information.
	 */
	public static final boolean debugAll = false;
	
	/**
	 * Number of Among constraints created.
	 */
	public static int counter  = 1;
		
	//All variables attributes
	private HashMap<IntVar, Integer> xIndex;
	private HashMap<IntVar, Integer> yIndex;
	
	//Derived variables
	
	// FIXME, check if timestamp over IntervalDomain is not better/cleaner.
	private MutableVar lbS;
	private MutableVar futureLbS;
	
	private LinkedHashSet<Integer> variableQueueY = new LinkedHashSet<Integer>();
	
	//Time stamps
	private TimeStamp<Integer> lb0TS;
	private TimeStamp<Integer> ub0TS;
	
	private TimeStamp<Integer> yGrounded;
	private TimeStamp<Integer> xGrounded;

	/**
	 * List of variables x which values are checked against values of variables y. Each x 
	 * is counted only once as equal to one of the elements of list y.
	 */
	public IntVar[] listOfX;
	
	/**
	 * It specifies what values we are counting in the list of x's. 
	 */
	public IntVar[] listOfY;	
	
	/** 
	 * It specifies the number of x variables equal to at least one value present in the list of y. 
	 */
	public IntVar n;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"listOfX", "listOfY", "n"};

	/**
	 * It constructs an AmongVar constraint. 
	 * @param listOfX the list of variables whose equality to other set of variables we count
	 * @param listOfY the list of variable to which equality is counted.
	 * @param n how many variables from list x are equal to at least one variable from list y.
	 */
	public AmongVar(IntVar[] listOfX, IntVar[] listOfY, IntVar n) {
	
		this.queueIndex = 1;
		
		numberId = counter ++;
		this.numberArgs = (short) ( listOfX.length + listOfY.length + 1);
				
		this.listOfX = new IntVar[listOfX.length];
		for (int i = 0; i < listOfX.length; i++){
			assert (listOfX[i] != null) : i + "-th element in listOfX is null";
			this.listOfX[i] = listOfX[i];
		}
		
		this.listOfY = new IntVar[listOfY.length];
		for (int i = 0; i < listOfY.length; i++){
			assert (listOfY[i] != null) : i + "-th element in listOfY is null";
			this.listOfY[i] = listOfY[i];
		}	
		
		assert (n != null) : "Variable n is null";
		this.n = n;	
	}

	/**
	 * It constructs an AmongVar constraint. 
	 * @param listOfX the list of variables whose equality to other set of variables we count
	 * @param listOfY the list of variable to which equality is counted.
	 * @param n how many variables from list x are equal to at least one variable from list y.
	 */
	public AmongVar(ArrayList<IntVar> listOfX, ArrayList<IntVar> listOfY, IntVar n) {
		
		this(listOfX.toArray(new IntVar[listOfX.size()]), listOfY.toArray(new IntVar[listOfY.size()]), n);

	}
	
	@Override
	public ArrayList<Var> arguments() {
		ArrayList<Var> variables = new ArrayList<Var>(this.numberArgs-1);

		variables.add(this.n);
        variables.addAll(Arrays.asList(this.listOfX));
        variables.addAll(Arrays.asList(this.listOfY));

		return variables;
	}

	@Override
	public void removeLevel(int level) {
		this.variableQueueY.clear();
	}

	
	/**
	 * Is called when all y are grounded and amongForSet is equivalent to simple version of Among.
	 * @param store constraint store in which context that consistency function is being executed.
	 */
	public void consistencyForX(Store store) {
		
		IntDomain lbSDom = (IntDomain)((MutableDomainValue)lbS.value()).domain;
		
		int lb0 = lb0TS.value();
		int ub0 = ub0TS.value();
		
		IntVar x, tmpX;
		
		boolean inLb = false;
		
		for (int i = lb0; i < ub0; i++) {
			x = listOfX[i];
			inLb = false;
			// watch the relation with lbS
			if (lbSDom.getSize() >0)
				if (lbSDom.contains(x.domain)) {		
					//put in the beginning  of the array
					if (i != lb0) {
						tmpX = listOfX[lb0];
						listOfX[lb0] = x;
						listOfX[i] = tmpX;
						xIndex.put(x, lb0);
						xIndex.put(tmpX, i);
					}
					lb0++;
					inLb = true;
					x.removeConstraint(this);						
				}	
			
			if (!inLb )
				if (!lbSDom.isIntersecting(x.domain)) {
					//X is not intersecting the domain of y
					//put at the end of the array
					if (i != ub0 - 1) {
						tmpX= listOfX[ub0-1];
						listOfX[ub0-1] = x;
						listOfX[i] = tmpX;
						xIndex.put(x, ub0-1);
						xIndex.put(tmpX, i);
					}
					ub0--;
					i--;
					x.removeConstraint(this);
				}
		}

		if (lb0 != lb0TS.value()) lb0TS.update(lb0);
		if (ub0 != ub0TS.value()) ub0TS.update(ub0);		
		
		if (debugAll) {
			System.out.println("-------------Consistency FOR X -------------");
			System.out.println("--LEVEL : " + store.level);
			System.out.println(this);
			System.out.println("--lbS = " +lb0);
			System.out.println("--ubS = " +ub0);
			System.out.println("------------");
		}
		
		int minN = Math.max(n.min(),lb0);
		int maxN = Math.min(n.max(), ub0);
		
		if (minN > maxN)
			throw Store.failException; 
		
		n.domain.in(store.level, n, minN, maxN);
		
		if (debugAll)
			System.out.println("-- K =  " + lbSDom);
		
		if (n.domain.singleton()) {
			
			if (lb0 == n.min() && ( ub0) == n.min()) {
				this.removeConstraint();
				return;
			}
			
			if (lb0 == n.min()) {			
				for (int i = lb0; i < ub0; i++) {
					x = listOfX[i];	
						
					x.domain.in(store.level, x, x.domain.subtract(lbSDom));
					if (debugAll) System.out.println("-- " + x.id()+ " in " + x.domain);
				}
			}
		
			if ( ub0 == n.min()) {			
				for (int i = lb0; i < ub0; i++) {
					x = listOfX[i];
					x.domain.in(store.level, x, x.domain.intersect(lbSDom));
					if (debugAll)  
						System.out.println("-- " + x.id()+ " in " + x.domain);
				}				
			}
		}		
	}
	
	/**
	 * The number of x in lbsDom is equal to the number of X intersecting ubSDom.
	 * 
	 * 1) If there are not enough of y to cover future domain then fail
	 * 2) 
	 * 
	 * @param store
	 */
	public void consistencyWhen_LB0_EQ_UB0(Store store) {
		
		IntDomain lbSDom = (IntDomain)((MutableDomainValue) lbS.value()).domain;
		IntDomain futureDom =  (IntDomain)((MutableDomainValue) futureLbS.value()).domain;
		IntVar y;
		int i;
		//number of grounded Y
		int yGround = yGrounded.value();
		//number of Y that can potentially cover some X
		int potentialCover = 0;
		for (i = yGround; i < listOfY.length; i++){
			y = listOfY[i];
			if (y.domain.isIntersecting(futureDom))
				potentialCover ++;
		}
		
		if (debugAll) {
			System.out.println("-------------Consistency when LB0 == UB0 -------------");
			System.out.println("--LEVEL : " + store.level);
			System.out.println("--lbSDom  = " +lbSDom);
			System.out.println("--futureDom  = " +futureDom);
			System.out.println("covered min " + yGround);
			System.out.println("left y that may play role" + potentialCover );
			System.out.println("------------");
		}
	
	
		if (potentialCover < futureDom.getSize()) {
			if (debugAll) 
				System.out.println("Fail beacuase there are not enough of y to cover x");
			throw Store.failException;
		}
			
		if (potentialCover == futureDom.getSize()) {
			if (debugAll) {
				System.out.println("if the number of y is just enough to cover future domain");
				System.out.println("than we can decrease their domain to future dom");
				System.out.println("and detauch those who are not intersecting the future dom");
			}
			
			for (i = yGround; i < listOfY.length; i++){
				y = listOfY[i];
				if (y.domain.isIntersecting(futureDom))
					y.domain.in(store.level, y, y.domain.intersect(futureDom));			
				else
					y.removeConstraint(this);
					
			}
		}
			
	}
	
	
	/**
	 * It is a function which makes Y consistent if all X's are grounded.
	 * @param store a constraint store in which context all prunings are executed.
	 */
	public void consistencyForY(Store store)
	{
	
		IntDomain K = new IntervalDomain();
		for (IntVar x : listOfX)
			if (x.singleton())
				K = K.union(x.min());
			else {
				assert (false) : "consistencyForY is called without all X being grounded";
				return;
			}	
		
		IntDomain lbSDom = (IntDomain)((MutableDomainValue) lbS.value()).domain;
		IntDomain futureDomain = (IntDomain)((MutableDomainValue) futureLbS.value()).domain;		
		IntDomain U = null;
		
		if (lbSDom.getSize() > 0) {
			if (futureDomain.getSize() > 0) U = lbSDom.subtract(futureDomain);
			else U = (IntDomain)lbSDom.clone();
		}
		else U = new IntervalDomain();
		
		if (debugAll) {
			System.out.println("-------------Consistency FOR Y -------------");
			System.out.println("--LEVEL : " + store.level);
			System.out.println(this);
			System.out.println("--x formed K = " +K);
			System.out.println("--y formed U = " +U);
			System.out.println("------------");
		}
		
		int yGr = this.yGrounded.value();
		int ub0 = this.ub0TS.value();
		IntVar y;
		IntVar x;
		
		//number of X that are already covered by some y
		int countCoverMin = 0;
		//Number of Y who are not playing role in covering x
		int noRoleY = 0;
		//Number of Y who might cover x that were not yet covered
		int potentialCover = 0;
		
		//Number of Y who already covering some x
		int alreadyCover = 0;
		
		//Number of disjoint Y who will cover x that were not yet covered
		int disjointCover = 0;
		
		for (int i = 0; i<ub0; i++) {
			x = this.listOfX[i];
			if (U.contains(x.value())) countCoverMin++;
		}
			
		for (int i = 0; i < yGr; i++) {
			y = listOfY[i];
			if (K.contains(y.domain))
				alreadyCover++;
			else
				noRoleY++;
		}
		
		IntDomain intersectK = new IntervalDomain();
		IntDomain disjoint = new IntervalDomain();
		for (int i = yGr; i < listOfY.length; i++) {
			y = listOfY[i];
			if (y.singleton()){
				if (K.contains(y.domain))
					alreadyCover++;
				else
					noRoleY++;		
			} else {
			
				intersectK = (y.domain.intersect(K)).subtract(U);
			
				if (intersectK.getSize()==0) 
					noRoleY++;
				else
					if (intersectK.getSize()==y.domain.getSize()) {
						potentialCover++;	
						if (!disjoint.isIntersecting(y.domain))	{
							disjointCover++;
							disjoint = disjoint.union(y.domain);
						}
					}				
					else
						potentialCover ++;		
			}
		}
		
		if (debugAll) { 
			System.out.println("--number of x already covered=       " +countCoverMin);
			System.out.println("--number of y that already cover x = " +alreadyCover);
			System.out.println("--number of no role y=               " +noRoleY);
			System.out.println("--number of potential cover y=       " +potentialCover);
			System.out.println("--min nb of y for disjoint cover=    " +disjointCover);
			System.out.println("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%");
		}
		
		if (countCoverMin > n.max()) {
			if (debugAll) 
				System.out.println("........Fail because the number of covered X is bigger than N........");					
			throw Store.failException;
		}
		
		if ( noRoleY == (listOfY.length - alreadyCover )) {
			if (debugAll) 
				System.out.println("........N must be equal to " + countCoverMin);
			n.domain.in(store.level, n, countCoverMin, countCoverMin);
		}
		
		K = K.subtract(U);
		
		if ( (countCoverMin == n.min()) && n.singleton() ) {
			
			if (debugAll)  
				System.out.println("--K \\ U = " + K );
			
			for (int i=yGr; i < listOfY.length; i++)
			{
				y = listOfY[i];
				if (y.domain.isIntersecting(K)){
					y.domain.in(store.level, y, y.domain.subtract(K));
				}
			}
			return;
		}

		int mayLeftToCover = listOfX.length - ub0;
		for (int i = 0; i < ub0; i++) {
			x = listOfX[i];
			if (K.contains(x.min())) 
				mayLeftToCover ++;
		}

		if ( K.getSize() == mayLeftToCover) {
			n.domain.in(store.level, n,countCoverMin + disjointCover, countCoverMin+potentialCover);
		}
		
		if (n.singleton()) {
			if (potentialCover <= K.getSize() && mayLeftToCover == (n.min() - countCoverMin) && K.getSize() == mayLeftToCover) {
				for (int i = yGr; i < listOfY.length; i++) {
					y = listOfY[i];
					if (y.domain.isIntersecting(K)) {
						y.domain.in(store.level, y, K);
					}
				}
			}
			if ( potentialCover == n.min()- countCoverMin &&  K.getSize() == mayLeftToCover) 
				for (int i = yGr; i < listOfY.length; i++) {
					y = listOfY[i];
					if (y.domain.isIntersecting(K)) {
						y.domain.in(store.level, y, K);
					}
				}
		}
	}
		
	@Override
	public void consistency(Store store) {
				
		//pureUbs ubs usually equals to ubs \ lbs and is used upon calculating 
		//the lbV and ubV hashtables
		IntervalDomain pureUbs = new IntervalDomain();
		Hashtable<Integer,Integer> lbV = new Hashtable<Integer,Integer>();
		Hashtable<Integer,Integer> ubV = new Hashtable<Integer,Integer>();
		
		//Take the lbs domain computed on the previous level
		//it contain the Y values that will be or must be present in S domain
		IntDomain lbSDom  = (IntDomain)((MutableDomainValue)this.lbS.value()).domain;
		
		//Ubs domain must be recalculated on the each level because the 
		//shrinking of the Y domain will cause ubs's decrease
		IntDomain ubSDom  = null;
		if (lbSDom.getSize() > 0 ) 
			ubSDom = (IntDomain)lbSDom.clone();
		else 
			ubSDom = new IntervalDomain();
		
		//Future domain contains the Y values that are not must be present in S
		//meaning that one (or more) Y must be grounded to such values
		IntDomain futureDom =  (IntDomain)((MutableDomainValue)this.futureLbS.value()).domain;
		
		//mustBeCoveredNow consists of the Y values that must be present in lbs 
		//but they were pruned out from some Y domain, and thus need a check-up
		IntervalDomain mustBeCoveredNow = new IntervalDomain();
		
		//we will count the number of new grounded Y in order to move such Y
		//in the beginning of the array and move the pointer. It helps to avoid 
		//some recalculations and give potential to fail if the number of ungrounded Y
		//is not enough to cover the future domain
//		int countGY = 0;	
		IntVar y;
		int lastIndex = yGrounded.value();
		IntervalDomain lbVubV = new IntervalDomain();
		
		boolean skipInitialLB0UB0calculation = false;

		boolean firstTimeWhileLoop = true;

		while (variableQueueY.size() > 0 || firstTimeWhileLoop) {
			
			//----------------------------------------------------------
			if (debugAll) {
				System.out.println("LEVEL : " + store.level);
				System.out.println(this);
			}
			//----------------------------------------------------------
					
			pureUbs.clear();
			//Construction of lbSDom
			while (variableQueueY.size() > 0) {
				for (Integer yi: this.variableQueueY) {
					y = this.listOfY[yi];
					if (y.singleton()) {
						if (debugAll) 
							System.out.println("New y " + y.id+ " was grouded to " + y.value());
						//Increase the lbSDom with grounded y
						lbSDom = lbSDom.union(y.domain);		
						if (futureDom.getSize() > 0) 
							futureDom = futureDom.subtract(y.value(), y.value());
						if  (y.domain.previousDomain() != null) {
							mustBeCoveredNow =(IntervalDomain) mustBeCoveredNow.union((y.domain.previousDomain()));
							if (! firstTimeWhileLoop) 
								pureUbs = (IntervalDomain)pureUbs.union((y.domain.previousDomain()) );
						}
//						countGY ++;			
						
						if (yi >= lastIndex) {
							if (yi != lastIndex) {
								int yInt = yi;
								IntVar tmp = listOfY[lastIndex];
								listOfY[lastIndex] = y;
								listOfY[yInt] = tmp;
								yIndex.put(y, lastIndex);
								yIndex.put(tmp, yInt);
							}
							lastIndex ++;
						}															
					} else {
						if (! firstTimeWhileLoop)						
							if  (y.domain.previousDomain() != null)
								pureUbs = (IntervalDomain)pureUbs.union((y.domain.previousDomain()) );
						if  ((y.domain.previousDomain()) != null)
							mustBeCoveredNow =(IntervalDomain) mustBeCoveredNow.union((y.domain.previousDomain()));
						}	
				}
				variableQueueY.clear();
				yGrounded.update(lastIndex);
				
				if (futureDom.getSize() > 0) 
					mustBeCoveredNow =(IntervalDomain) mustBeCoveredNow.intersect(futureDom);
				else 
					mustBeCoveredNow = (IntervalDomain)futureDom;
				
				//If there appeared the Y values that have a risk to stay ungrounded
				//we will count their cardinality and FAIL if its 0, ground some Y if it is 1
				if (mustBeCoveredNow.getSize() > 0) {	
					if (debugAll) 
						System.out.println("It appears that we must cover such values : "+ mustBeCoveredNow);
					int cardinalityV = 0;
					int last;
					IntVar y_last;
					//Go though all the intervals of the domain
					
					Interval inv;
					for (int h = 0; h < mustBeCoveredNow.size; h++) {
						inv =  mustBeCoveredNow.intervals[h];
						//go through each value of the interval						
						for (int v = inv.min; v <= inv.max; v++) {								
						    cardinalityV =0;						   
							last=-1;
							//count the cardinality of v among Y
							for (int i = this.yGrounded.value(); i < this.listOfY.length; i++) {
								y = this.listOfY[i];
								
								if (y.singleton() && y.min() == v) {
									mustBeCoveredNow = mustBeCoveredNow.subtract(v, v);
									cardinalityV = -1;
									break;
								}
								if (y.domain.contains(v)) {
									cardinalityV ++;
									last = i;
								}
							}
							if (cardinalityV == 0) {
								if (debugAll) 
									System.out.println("Cardinality of " +v+ " is 0 => FAIL ");
								throw Store.failException;
							}
							else if (cardinalityV == 1) {
								y_last = this.listOfY[last];
								if (debugAll) 
									System.out.println("Cardinality of " +v+ " is 1 => Groud " + y_last.id);
								
								if (last != lastIndex) {
									int yInt = last;
									IntVar tmp = listOfY[lastIndex];
									listOfY[lastIndex] = y_last;
									listOfY[yInt] = tmp;
									yIndex.put(y_last, lastIndex);
									yIndex.put(tmp, yInt);
								}
								lastIndex ++; 
								y_last.domain.in(store.level, y_last, v,v);
								
								mustBeCoveredNow = mustBeCoveredNow.subtract(v, v);
							}											
						}
					}
				}		
			}
			lbS.update(new MutableDomainValue(lbSDom));
			mustBeCoveredNow = new IntervalDomain();
			futureLbS.update(new MutableDomainValue(futureDom));
			
			if (debugAll) {
				// System.out.println(countGY + " new y were grounded and " +(this.yGrounded.value()) + " in general");
				System.out.println("Future domain is " + futureDom);	
			}
			
			if ( this.listOfY.length - this.yGrounded.value() < futureDom.getSize()) {
				if (debugAll) 
					System.out.println("Fail because the number of not grounded y is not enough to cover future lbS domain");
				throw Store.failException;
			}
			if (this.yGrounded.value() == this.listOfY.length) {
				if (debugAll) 
					System.out.println("All Y were grounded, thus we can pass to simple ve rsion of Among contrians where GAC can be reached");
				consistencyForX(store);
				return;
			}
			
			for (IntVar var: this.listOfY) {
				 ubSDom = ubSDom.union(var.domain);
			}	
			
			//----------------------------------------------------------
			if (debugAll) {
				System.out.println("lbS = " +lbSDom);
				System.out.println("ubS = " +ubSDom);
				System.out.println("--------");
			}
			//----------------------------------------------------------
			
			//Next part of consistency count occupy the X variables: count the lb0, glb0, ub0, lub0
			int lb0 = lb0TS.value();
			int ub0 = ub0TS.value();
			
			int glb0 = lb0;			
			
			// [x1, x2, x3, ... x_lb0] ..... [ x_ub0 .... x_n] 
			
			//lbSDOm and ubSDom are ready
			IntVar x;
			IntVar tmpX;
			if (!skipInitialLB0UB0calculation){
				for (int i = lb0; i < ub0; i++) {
					x = listOfX[i];
					//a) count the grounded x
					
					//b) watch the relation with lbS
					if (lbSDom.getSize() > 0)
						if (lbSDom.contains(x.domain)) {
							
							//put in the beginning  of the array
							if (i != lb0) {
								tmpX = listOfX[lb0];
								listOfX[lb0] = x;
								listOfX[i] = tmpX;
								xIndex.put(x, lb0);
								xIndex.put(tmpX, i);
							}
							lb0++;
							glb0 ++;
							
							x.removeConstraint(this);
							
						} else if (lbSDom.isIntersecting(x.domain)) {
								glb0 ++;						
						}	
			
									
					if (!ubSDom.isIntersecting(x.domain)) {
						//X is not intersecting the domain of y
						//put at the end of the array
						if (i != ub0 - 1) {
							tmpX= listOfX[ub0-1];
							listOfX[ub0-1] = x;
							listOfX[i] = tmpX;
							xIndex.put(x, ub0-1);
							xIndex.put(tmpX, i);
						}
						ub0--;
						i--;
						x.removeConstraint(this);
					}					
				
				}
			
				if (lb0 != lb0TS.value()) lb0TS.update(lb0);
				if (ub0 != ub0TS.value()) ub0TS.update(ub0);
			}
			
			if (this.satisfied()) return;
			
			if (debugAll) {
				System.out.println("--------");
				System.out.println("- lb0  = " + lb0);
				System.out.println("- glb0 = " + glb0);
				System.out.println("- ub0  = " + ub0);
				System.out.println(" domain of N " + n.domain + " is in [ " +  Math.max(n.min(),lb0) + ", " +  Math.min(n.max(), ub0) +" ]" );
				System.out.println("--------");
			}
					
			int minN = Math.max(n.min(),lb0);
			int maxN = Math.min(n.max(), ub0);
			
			if (minN > maxN)
				throw Store.failException;
			
			n.domain.in(store.level, n, minN, maxN);
			
			/*----------------------------------------------------------
			 Now we will enter the pruning N part
			 For each value of UBS we will calculate : 
			 lbV - lower border on N if v was included into S
			 weight - max number of X which can take value from S if v was included into S 
			 ubV - upper border on N if v as excluded from S
			 _____________________________________________________
			 lbV - lb0 gives min number of X which can take value from S if v was included into S
			
			 N must be in the Union[ (lbV - lb0 ), weight] and their combinations
			  
			
			*/
			int lbTmp =  0;
			int ubTmp =  0;
			int weight = 0;
			
			
			if (firstTimeWhileLoop){
				lbVubV = new IntervalDomain(lb0, glb0);
				lbVubV = (IntervalDomain)lbVubV.union(ub0);	
			}
			
			
			int LB = Integer.MAX_VALUE;
			int UB = Integer.MIN_VALUE;
			if (firstTimeWhileLoop) 
				pureUbs= (IntervalDomain)ubSDom.subtract(lbSDom);
			else
				pureUbs = (IntervalDomain)pureUbs.intersect(ubSDom.subtract(lbSDom));
			
			Interval inv;
			
	
			for (int h=0; h<(pureUbs).size; h++) {
				inv = (pureUbs).intervals[h];
				//for each interval of UBS
				if (inv!=null)
					//For each value of the interval
					for (int v = inv.min; v <= inv.max; v++) {
						lbTmp =lb0;
						weight =0;
						ubTmp =0;
						
						for (int i = 0; i < lb0; i++) {
							x = listOfX[i];
							if (ubSDom.subtract(v,v).isIntersecting(x.domain))
								ubTmp++;
						}
							
						
						for (int i = lb0; i < ub0; i++) {
							x = listOfX[i];
							//a) count the weight
							if (firstTimeWhileLoop)
								if (x.domain.contains(v)) weight++;
							//b)count the relation with lbS
							if (lbSDom.union(v).contains(x.domain))
								lbTmp++;
							//c)count the relation with ubs
							if (ubSDom.subtract(v,v).isIntersecting(x.domain))
								ubTmp++;
							
						}
						if (debugAll) System.out.println("--- lb[" + v + "] = " + lbTmp);
						if (debugAll) System.out.println("--- ub[" + v + "] = " + ubTmp);
						lbV.put(v,lbTmp);
						ubV.put(v,ubTmp);			
						if ( ubTmp > UB)
							UB = ubTmp;
						
						if ( lbTmp < LB)
							LB = lbTmp;
						
						if (debugAll) 
							if (firstTimeWhileLoop)
							System.out.println("--- weight[" + v + "] = " + weight);
						
						if (firstTimeWhileLoop)
							if ( weight != 0)
								if ( (!lbVubV.contains(n.domain) ) ) {
									int max = 0;
									int min = 0;
									lbTmp = lbTmp-lb0;
								
									if (lbVubV.getSize() > 0)
										for (Interval a : lbVubV.intervals)
										{
											if (a != null )
											{
												max = Math.min( weight+ a.max, ub0);
												min = Math.max( lbTmp+a.min,lb0);
										
												if ( min <= max) 
												{
													lbVubV = (IntervalDomain)lbVubV.union(min, max );									
													if (debugAll)
														if ( a != null ) 
															System.out.println(" >>>> " + a + " + [" +lbTmp + ", " +weight+  "] = [" +min + ", " + max+  " ]");
												}else
													if (debugAll)
														if ( a != null ) 
														System.out.println(" >>>> " + a + " + [" +lbTmp + ", " +weight+  "] = NOTHING");
																										
											}
										}								
								}		
					}			
			}
			
			if (debugAll) 	
				System.out.println(" Made up n domain = " + lbVubV);
	
		   if (firstTimeWhileLoop)
			   n.domain.in(store.level, n, lbVubV.intersect(n.domain));

		   else n.domain.in(store.level, n, Math.max(lb0, n.min()), Math.min(ub0, n.max()));
			   			
			boolean recalculateLB0 = false;
			boolean recalculateUB0 = false;
			
			pureUbs = (IntervalDomain)ubSDom.subtract(lbSDom);
			
			for (int h = 0; h < pureUbs.size; h++) {
				inv =  pureUbs.intervals[h];
				if (inv != null){
					
					for (int v = inv.min; v <= inv.max; v++) {
						if (debugAll) System.out.println(">>>>>>>>>>>>>>>>>>>" + v + "  ");
						if (ubV.get(v) < n.min()){
							if (debugAll) System.out.println(v + " must be be present in S");
							lbSDom = lbSDom.union(v);
							recalculateLB0 = true;
							
							int cardinalityV =0;
							int last = -1;
							IntVar y_last = null;
							for (int i = this.yGrounded.value(); i < this.listOfY.length; i++) {
								y = this.listOfY[i];
								
								if (y.domain.contains(v)) {
									cardinalityV ++;
									last = i;
								}
							}
							
							
							if (cardinalityV == 1 )	{
								y_last = this.listOfY[last];
								if (!(y_last.singleton())) {
									y_last = this.listOfY[last];
									
									if (debugAll) 
										System.out.println("Only " + y_last.id + " can cover " + v + " so I ground it");
									
									mustBeCoveredNow = (IntervalDomain)mustBeCoveredNow.union(y_last.domain.subtract(v, v));
									
									int yInt = last;
									
									if (last != lastIndex) {
										IntVar tmp = listOfY[lastIndex];
										listOfY[lastIndex] = y_last;
										listOfY[yInt] = tmp;
										yIndex.put(y_last, lastIndex);
										yIndex.put(tmp, yInt);
									}
									lastIndex ++; 
									
									y_last.domain.in(store.level, y_last, v,v);
									
								}
							}
							else {
								if (cardinalityV == 0) throw Store.failException; 
								futureDom = futureDom.union(v);
							}
							
							
						}
						
						if (lbV.get(v) > n.max()){
							ubSDom = ubSDom.subtract(v, v);
							recalculateUB0 = true;
						
							if (debugAll) System.out.println(v + " must be pruned out of all y");
							
							for (int i = yGrounded.value(); i < listOfY.length; i++) {
								y = listOfY[i];
								
								if (y.singleton()) { 
									if (y.value() == v) throw Store.failException;
								}
								else {
									y.domain.inComplement(store.level, y, v);
									if (y.singleton()){
										if (futureDom.getSize()>0) futureDom = futureDom.subtract(y.value(), y.value());
										lbSDom = lbSDom.union(y.value());
										recalculateLB0 = true;
										
										if (i != lastIndex)
										{
											variableQueueY.remove(i);
											int yInt = i;
											IntVar tmp = listOfY[lastIndex];
											listOfY[lastIndex] = y;
											listOfY[yInt] = tmp;
											yIndex.put(y, lastIndex);
											variableQueueY.add(lastIndex);
											yIndex.put(tmp, yInt);
										}
										lastIndex ++; 
									}
								}
							}
						}				
					}
				}
			}
			
			if (debugAll)  System.out.println("Future domain is " + futureDom);
			this.futureLbS.update(new MutableDomainValue(futureDom));
			
			skipInitialLB0UB0calculation = false;
			if (recalculateLB0 || recalculateUB0)
			{
				skipInitialLB0UB0calculation = true;
				boolean inLb = false;
				for (int i = lb0; i < ub0; i++) {
					x = listOfX[i];
					inLb = false;
					
					// watch the relation with lbS
					if (lbSDom.getSize() >0)
						if (lbSDom.contains(x.domain))
						{		
							//put in the beginning  of the array
							if (i != lb0)
							{
								tmpX= this.listOfX[lb0];
								this.listOfX[lb0] = x;
								this.listOfX[i] = tmpX;
								this.xIndex.put(x, lb0);
								this.xIndex.put(tmpX, i);
								
							}
							lb0++;
							inLb = true;
							x.removeConstraint(this);						
						}	
					
					if (!inLb && recalculateUB0 )
						if (!ubSDom.isIntersecting(x.domain)){
							//X is not intersecting the domain of y
							//put at the end of the array
							if (i != ub0-1)
							{
								tmpX = listOfX[ub0-1];
								listOfX[ub0-1] = x;
								listOfX[i] = tmpX;
								xIndex.put(x, ub0-1);
								xIndex.put(tmpX, i);
							}
							ub0--;
							i--;
							x.removeConstraint(this);
						}
				}

				if (lb0 != lb0TS.value()) lb0TS.update(lb0);
				if (ub0 != ub0TS.value()) ub0TS.update(ub0);
			}
			
			lbS.update(new MutableDomainValue(lbSDom));
			
			if (debugAll)
				{
				System.out.println("lb(S) := lb(S) U {v | ub[v] < min(N) } = " +  lbSDom );
				System.out.println("ub(S) := ub(S) \\ {v | lb[v] > max(N) } = " +  ubSDom );
				System.out.println("(min(N) = max(N)) = " + n.singleton());
				System.out.println("- lb0  = " + lb0);
				System.out.println("- ub0  = " + ub0);
				System.out.println(" domain of N " + n.domain + " is in [ " +  Math.max(n.min(),lb0) + ", " +  Math.min(n.max(), ub0) +" ]" );
				
				}
			
			n.domain.in(store.level, n, Math.max(n.min(),lb0), Math.min(n.max(), ub0));
			
			if (lbSDom.getSize() > ubSDom.getSize()  || lbSDom.getSize() > listOfY.length   ) {
				if (debugAll) 
					System.out.println("........Fail because lbSDom.getSize() > ubSDom.getSize()  || lbSDom.getSize() > this.yVarList.length........");
				throw Store.failException;
			}
			
			
			if (n.singleton()){	
				if (lbSDom.getSize() > 0) {
					if (n.value() == lb0)
						for (int i = lb0; i < ub0; i++) {
							x = listOfX[i];
							x.domain.in(store.level, x, x.domain.subtract(lbSDom));
						}
				}
				if (n.value()==ub0)					
					for (int i = lb0; i < ub0; i++) {
						x = listOfX[i];
						x.domain.in(store.level, x, x.domain.intersect(ubSDom));							
					}		
			}
			
			if (xGrounded.value() == listOfX.length) {
				consistencyForY(store);
			}
			else 
				if (lb0 == ub0)
					consistencyWhen_LB0_EQ_UB0(store);
			
			if (satisfied() ) {
				removeConstraint();
				return;
			}
			
			if (debugAll) System.out.println(this);
				
			firstTimeWhileLoop = false;
		}
	}
	
	@Override
	public int getConsistencyPruningEvent(Var var) {
//		 If consistency function mode
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.ANY;
	}

	@Override
	public void impose(Store store) {

		store.registerRemoveLevelListener(this);
		
		xIndex = new HashMap<IntVar, Integer>();
		
		int i = 0;
		IntVar y;
		IntVar x;
		int gx = 0;
		
		
		for (i = 0; i < listOfX.length; i++) {
			x = listOfX[i];
			x.putConstraint(this);
			xIndex.put(x, i);
			if (x.singleton()) gx++;
		}
		
		yIndex = new HashMap<IntVar, Integer>();
		
		for (i = 0; i < listOfY.length; i++) {
			y = listOfY[i];
			y.putConstraint(this);
			variableQueueY.add(i);
			yIndex.put(y, i);
		}
		
		n.putConstraint(this);
		
		lbS = new MutableDomain(store);
		futureLbS = new MutableDomain(store);
		
		lb0TS = new TimeStamp<Integer>(store, 0);
		ub0TS = new TimeStamp<Integer>(store, listOfX.length);
		
		xGrounded = new TimeStamp<Integer>(store, gx);
		yGrounded = new TimeStamp<Integer>(store, 0);
		
		store.addChanged(this);
		store.countConstraint();
		
		store.raiseLevelBeforeConsistency = true;
		
		
	}

	@Override
	public void queueVariable(int level, Var var) {
		
		if (debugAll) {
			System.out.println(" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% ");
			System.out.println("Var " + var + ((IntVar)var).recentDomainPruning());
		}

		
		int i;
		for (i = 0; i < this.listOfY.length; i++)
			if (this.listOfY[i] == var) {
				this.variableQueueY.add(i);
				return;
			}
				
		
		if (var != this.n) {
			//It can be only X
			if (var.singleton()) xGrounded.update( xGrounded.value() + 1);
		}
		
	}

	@Override
	public void removeConstraint() {
		if (debugAll) {
			System.out.println("............Finished with..............");
			System.out.println(this);
			System.out.println("..................................");
		}
		
		for (Var var : listOfX)
			var.removeConstraint(this);
		
		for (Var var : listOfY)
			var.removeConstraint(this);
		
		n.removeConstraint(this);
		
		this.variableQueueY.clear();
		
	}

	@Override
	public boolean satisfied() {
		
		if (n.singleton()) {
			
			int lb0 = lb0TS.value();
			int ub0 = ub0TS.value();
			
			boolean allYGrounded = (yGrounded.value() == listOfY.length);
			boolean allXGrounded = (xGrounded.value() == listOfX.length);
					
			if (allYGrounded) {
				if (n.value() == lb0 && lb0 == ub0) 
					return true;	    
			}
			
			if (allYGrounded && allXGrounded)
				assert (n.value() == lb0) : " Domain of N or value of timestamp LBoUTS was not maintenated properly";
		
		}
		return false;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );

		for(IntVar var : this.listOfX) {
			result.append("X variable ").append(var.id).append(" : ").append(var.domain);
			result.append(" 			among attached : ");
			result.append(var.domain.constraints().contains(this)).append(" \n");
		}
		
		for(IntVar var : this.listOfY) {
			result.append("Y variable ").append(var.id).append(" : ").append(var.domain);
			result.append(" 			among attached : ");
			result.append(var.domain.constraints().contains(this)).append(" \n");
		}

		result.append("variable ").append(n.id).append(" : ").append( n.domain );
		result.append(" 			among attached : ");
		result.append(n.domain.constraints().contains(this)).append("\n");
			
		return result.toString();
		
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			n.weight++;
			for (Var v : listOfX) v.weight++;
			for (Var v : listOfY) v.weight++;
		}
	}
	
}
