/**
 *  BoundSetDomain.java 
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

package org.jacop.set.core;

import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Defines a set interval determined by a least upper bound(lub) and a 
 * greatest lower bound(glb). The domain consist of zero, one or several sets.
 * 
 * 
 * @author Radoslaw Szymanek, Krzysztof Kuchcinski and Robert Åkemalm 
 * @version 4.2
 */

public class BoundSetDomain extends SetDomain {

	// FIXME do not use emptySet to assign to lub, glb. 
	/**
	 * The greatest lower bound of the domain.
	 */

	public IntDomain glb;

	/**
	 * The least upper bound of the domain.
	 */

	public IntDomain lub;

	/**
	 * The cardinality of the set. 
	 */

	public IntDomain cardinality;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"glb", "lub", "cardinality"};

	/** 
	 * 
	 * Creates BoundSetDomain object. It requires glb to be a subset of lub.
	 * 
	 * @param glb it specifies the left bound of the SetDomain (inclusive).  
	 * @param lub it specifies the right bound of the setDomain (inclusive).
	 * @param cardinality it specifies the allowed cardinality of the assigned set.
	 */
	public BoundSetDomain(IntDomain glb, IntDomain lub, IntDomain cardinality) {

		if(!lub.contains(glb))
			throw new IllegalArgumentException();

		this.glb = glb.cloneLight();
		this.lub = lub.cloneLight();
		this.cardinality = cardinality.cloneLight();

		searchConstraints = null;
		searchConstraintsToEvaluate = 0;
		previousDomain = null;
		searchConstraintsCloned = false;

	}


	/** Creates a new instance of SetDomain. It requires glb to be a subset of lub.
	 * @param glb it specifies the left bound of the SetDomain (inclusive).  
	 * @param lub it specifies the right bound of the setDomain (inclusive).
	 */
	public BoundSetDomain(IntDomain glb, IntDomain lub) {

		if(!lub.contains(glb))
			throw new IllegalArgumentException();

		this.glb = glb.cloneLight();
		this.lub = lub.cloneLight();
		this.cardinality = new IntervalDomain(glb.getSize(), lub.getSize());
		
		// TODO, test the replacement of intervaldomain when possible by SmallDenseDomain.
		//this.cardinality = new SmallDenseDomain(glb.getSize(), lub.getSize());
		
		searchConstraints = null;
		searchConstraintsToEvaluate = 0;
		previousDomain = null;
		searchConstraintsCloned = false;

	}

	/**
	 * It is a constructor which will create an empty SetDomain. An empty SetDomain
	 * has a glb and a lub that is empty.
	 */
	public BoundSetDomain() {

		this.glb = new IntervalDomain(0);
		this.lub = new IntervalDomain(0);
		
		searchConstraints = null;
		searchConstraintsToEvaluate = 0;
		previousDomain = null;
		searchConstraintsCloned = false;

	}

	/** 
	 * 
	 * It creates a new instance of SetDomain with glb empty and lub={e1..e2}
	 * @param e1 the minimum element of lub.
	 * @param e2 the maximum element of lub.
	 */
	public BoundSetDomain(int e1, int e2) {

		if (e2 - e1 > 63) {
			this.glb = new IntervalDomain(0);
			this.lub = new IntervalDomain(e1, e2);
		}
		else {
			this.glb = new SmallDenseDomain();
			this.lub = new SmallDenseDomain(e1, e2);			
		}
		
		this.cardinality = new IntervalDomain(0, e2 - e1 + 1);

		searchConstraints = null;
		searchConstraintsToEvaluate = 0;
		previousDomain = null;
		searchConstraintsCloned = false;

	} 

	/**
	 * Adds a set of value to the possible values used within this set domain. It changes the cardinality 
	 * too to avoid cardinality constraining the domain. 
	 * 
	 */
	public void addDom(IntDomain set) {

		assert set.checkInvariants() == null : set.checkInvariants() ;

		this.lub = this.lub.union(set);
		this.cardinality = new IntervalDomain(glb.getSize(), lub.getSize());

	}

	/**
	 * Adds a set to the domain.
	 */
	public void addDom(SetDomain domain) {

		assert domain.lub().checkInvariants() == null : domain.lub().checkInvariants() ;
		assert domain.glb().checkInvariants() == null : domain.glb().checkInvariants() ;

		lub = lub.union(domain.lub());
		glb = glb.intersect(domain.glb());
		this.cardinality = new IntervalDomain(glb.getSize(), lub.getSize());			

	}

	/**
	 * Adds an interval [min..max] to the domain.
	 * @param min min value in the set
	 * @param max max value in the set
	 */
	public void addDom(int min, int max) {
		this.addDom(new IntervalDomain(min,max));
	}

	/**
	 * Returns the cardinality of the setDomain as [glb.card(), lub.card()] 
	 * @return The cardinality of the setDomain given as a boundDomain.
	 */
	public IntDomain card(){
		return cardinality;
	}

	/**
	 * Sets the domain to an empty SetDomain.
	 */
	@Override
	public void clear() {
		glb = new IntervalDomain();
		lub = new IntervalDomain();
		this.cardinality = new IntervalDomain(0, 0);
	}

	/**
	 * Clones the domain.
	 */
	@Override
	public SetDomain clone() {

		BoundSetDomain cloned = new BoundSetDomain(glb.cloneLight(), lub.cloneLight()); 
		cloned.stamp = stamp;
		cloned.previousDomain = previousDomain;

		cloned.searchConstraints = searchConstraints;
		cloned.searchConstraintsToEvaluate = searchConstraintsToEvaluate;

		cloned.modelConstraints = modelConstraints;
		cloned.modelConstraintsToEvaluate = modelConstraintsToEvaluate;

		cloned.searchConstraintsCloned = searchConstraintsCloned;

		return cloned;	
	}

	/**
	 * It clones the domain object, only data responsible for encoding domain
	 * values is cloned. All other fields must be set separately.
	 * @return return a clone of the domain. It aims at getting domain of the proper class type. 
	 */
	public SetDomain cloneLight() {
		// FIXME, why no glb and lub cloning is safe?
		return new BoundSetDomain(glb, lub); 
		// 		return new SetDomain(glb.cloneLight(), lub.cloneLight()); 
	}

	/**
	 * It creates a complement of a domain.
	 * @return it returns the complement of this domain.
	 */
	public SetDomain complement() {
		// FIXME, is it right?
		// FIXME, it is not possible to express the complement of the set interval using just one set, right?
		return new BoundSetDomain(this.lub.complement(),this.glb.complement());		
	}

	/**
	 * It checks if the supplied set or setDomain is a subset of this domain.
	 */
	public boolean contains(IntDomain set) {

		assert set.checkInvariants() == null : set.checkInvariants() ;

		if(this.lub.contains(set))
			return true;
		
		return false;
	}

	public boolean contains(SetDomain domain) {

		assert domain.checkInvariants() == null : domain.checkInvariants() ;

		if(this.lub.contains(domain.lub()))
			return true;

		return false;
	}

	/**
	 * It checks if value belongs to the domain.
	 */
	public boolean contains(int value) {
		return lub.contains(value);
	}

	/**
	 * It returns an unique identifier of the domain.
	 * @return it returns an integer id of the domain.
	 */
	@Override
	public int domainID() {
		return SetDomainID;
	}

	/**
	 * It checks if the domain is equal to the supplied domain.
	 * @param domain against which the equivalence test is performed.
	 * @return true if suppled domain has the same elements as this domain. 
	 */
	public boolean eq(SetDomain domain) {
		if(domain.glb().eq(this.glb) && domain.lub().eq(this.lub))
			return true;
		return false;
	}

	/**
	 * Returns the number of elements in the domain.
	 */
	@Override
	public int getSize() {
		return (int) Math.pow(2, (lub.getSize() - glb.getSize()));
	}

	/**
	 * It returns the greatest lower bound of the domain.
	 * @return the greatest lower bound of the domain.
	 */
	public IntDomain glb() {
		return this.glb;
	}

	/**
	 * This function is equivalent to in(int storeLevel, Variable var, int min, int max).
	 *
	 * @param storeLevel the level of the store at which the change occurrs.
	 * @param var the set variable for which the domain may change.
	 * @param inGLB the greatest lower bound of the domain. 
	 * @param inLUB the least upper bound of the domain.
	 */
	public void in(int storeLevel, SetVar var, IntDomain inGLB, IntDomain inLUB) {

		// FIXME, this check should be done outside if it can be violated.
		if (!inLUB.contains(inGLB)){
			throw Store.failException;
		}

		// FIXME, do we need to do this expensive check in this manner, or at all here?
		if (glb.contains(inGLB) && inLUB.contains(lub)){
			// New domain is the same or "larger" than the old one; do nothing,
			// do not re-evaluate constrained assigned to this variable
			return; 
		}

		if (stamp == storeLevel) {

			int eventGLB = glb.unionAdapt(inGLB);
			int eventLUB = lub.intersectAdapt(inLUB);

			if (lub.eq(glb)) {
				cardinality.intersectAdapt(glb.getSize(), lub.getSize());
				if (cardinality.isEmpty())
					throw Store.failException;
				var.domainHasChanged(IntDomain.GROUND);
			}
			else {
				int eventCardinality = cardinality.intersectAdapt(glb.getSize(), lub.getSize());
				
				if (cardinality.isEmpty())
					throw Store.failException;
				
				if (eventCardinality != Domain.NONE) {
					
					if (cardinality.min() == lub.getSize()) {
						glb = lub;
						cardinality.intersectAdapt(lub.getSize(), lub.getSize());
						var.domainHasChanged(IntDomain.GROUND);
						return;
					}
					
					if (cardinality.max() == glb.getSize()) {
						lub = glb;
						cardinality.intersectAdapt(glb.getSize(), glb.getSize());
						var.domainHasChanged(IntDomain.GROUND);
						return;
					}

				}
				
				if (eventGLB != Domain.NONE && eventLUB != Domain.NONE)
					var.domainHasChanged(SetDomain.ANY);
				else 
					if (eventGLB != Domain.NONE)
						var.domainHasChanged(SetDomain.GLB);
					else if (eventLUB != Domain.NONE)
						var.domainHasChanged(SetDomain.LUB);
			}

			return;

		} else {

			assert stamp < storeLevel;

			IntDomain resultGLB = glb.cloneLight();
			int eventGLB = resultGLB.unionAdapt(inGLB);

			IntDomain resultLUB = lub.cloneLight();
			int eventLUB = resultLUB.intersectAdapt(inLUB);

			IntDomain resultCardinality = cardinality.intersect(glb.getSize(), lub.getSize());
			if (resultCardinality.isEmpty())
				throw Store.failException;			

			if (!resultCardinality.eq(cardinality)) {
				
				if (cardinality.min() == lub.getSize()) {
					resultGLB = lub;
					resultCardinality.intersectAdapt(lub.getSize(), lub.getSize());
				}
				
				if (cardinality.max() == glb.getSize()) {
					resultLUB = glb;
					resultCardinality.intersectAdapt(glb.getSize(), glb.getSize());
				}

			}

			BoundSetDomain result = new BoundSetDomain();
			result.glb = resultGLB;
			result.lub = resultLUB;
			result.cardinality = resultCardinality;

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			var.domain = result;

			if (result.singleton()) {
				var.domainHasChanged(SetDomain.GROUND);
				return;
			} else {

				if (eventGLB == SetDomain.GLB && eventLUB == SetDomain.LUB)
					var.domainHasChanged(SetDomain.BOUND);
				else if (eventGLB != Domain.NONE)
					var.domainHasChanged(SetDomain.GLB);
				else if	(eventLUB != Domain.NONE)
					var.domainHasChanged(SetDomain.LUB);
				return;
			}

		}	
	}


	/**
	 * It updates the domain to have values only within the domain. The type of
	 * update is decided by the value of stamp. It informs the variable of a
	 * change if it occurred.
	 * @param storeLevel level of the store at which the update occurs.
	 * @param var variable for which this domain is used.
	 * @param setDom the domain according to which the domain is updated.
	 */
	public void in(int storeLevel, SetVar var, SetDomain setDom) {
		in(storeLevel, var, setDom.glb(), setDom.lub());
	}

//	public void in(int storeLevel, SetVar var, IntDomain set) {
//		this.in(storeLevel, var, IntDomain.emptyIntDomain, set);
//	}

	/**
	 * It intersects current domain with the one given as a parameter.
	 * @param domain domain with which the intersection needs to be computed.
	 * @return the intersection between supplied domain and this domain.
	 */
	public SetDomain intersect(SetDomain domain) {

		assert domain.checkInvariants() == null : domain.checkInvariants() ;

		IntDomain lub_i = lub.intersect( domain.lub() );

		if( lub_i.isEmpty() )
			return emptyDomain;

		IntDomain glb_i = glb.intersect( domain.glb() ); 

		return new BoundSetDomain(glb_i,lub_i);
	}

	/**
	 * It intersects current domain with the one given as a parameter.
	 * @param domain domain with which the intersection needs to be computed.
	 * @return the intersection between supplied domain and this domain.
	 */

	public SetDomain intersect(IntDomain domain) {

		assert domain.checkInvariants() == null : domain.checkInvariants() ;


		IntDomain lubResult = lub.intersect(domain);

		if(lubResult.isEmpty())
			return emptyDomain;

		IntDomain glbResult = glb.intersect(domain); 

		return new BoundSetDomain(glbResult, lubResult);
	}

	/**
	 * It returns true if given domain is empty.
	 * @return true if the given domain is empty.
	 */
	@Override
	public boolean isEmpty() {
		if (glb.isEmpty() && lub.isEmpty())
			return true;
		return false;
	}

	/**
	 * It returns true if given domain intersects this domain.
	 * @return true if the given domain intersects this domain.
	 */
	// FIXME, improve the implementation.
	public boolean isIntersecting(SetDomain domain) {
		return !this.intersect(domain).isEmpty();
	}

	/**
	 * In intersects current domain with the interval min..max.
	 * @param min the left bound of the interval (inclusive)
	 * @param max the right bound of the interval (inclusive)
	 * @return the intersection between the specified interval and this domain.
	 */
	// FIXME, improve the implementation.
	public boolean isIntersecting(int min, int max) {
		return lub.isIntersecting(new IntervalDomain(min,max));
	}

	/**
	 * A set is never numeric
	 * @return false
	 */
	@Override
	public boolean isNumeric() {
		return false;
	}

	/**
	 * A set is not sparse
	 * @return false
	 */
	@Override
	public boolean isSparseRepresentation() {
		return false;
	}

	/**
	 * It returns the least upper bound of the domain.
	 * @return the least upper bound of the domain.
	 */
	public IntDomain lub() {
		return this.lub;
	}

	/**
	 * It sets the domain to the specified domain.
	 * @param domain the domain from which this domain takes all elements.
	 */
	public void setDomain(SetDomain domain) {

		assert domain.checkInvariants() == null : domain.checkInvariants() ;

		this.glb = domain.glb();
		this.lub = domain.lub();
		return;

	}

	/**
	 * It sets the domain to the the set {min..max}. It grounds it. 
	 * FIXME should it be grounded? 
	 */
	public void setDomain(int min, int max) {

		assert (min <= max);
		// FIXME, BUG?
		this.lub = new IntervalDomain(min, max);
		this.glb = new IntervalDomain();	

		// FIXME, remove after checking.
		throw new RuntimeException("check that the caller of this function is using it as intended.");

	}

	/**
	 * It returns true if given domain has only one set-element.
	 * @return true if the domain contains only one set-element.
	 */
	@Override
	public boolean singleton() {
		return (lub.eq(glb));
	}

	/**
	 * It returns true if given domain has only one set-element and this set-element only contains c.
	 * @return true if the domain contains only one set-element and this set-element only contains c.
	 */	
	public boolean singleton(IntDomain set) {

		return lub.eq(set) && glb.eq(set);

	}

	/**
	 * It subtracts domain from current domain and returns the result.
	 * @param domain the domain which is subtracted from this domain.
	 * @return the result of the subtraction.
	 */
	public SetDomain subtract(SetDomain domain) {

		assert domain.checkInvariants() == null : domain.checkInvariants() ;

		IntDomain glbResult = glb.subtract( domain.lub() );	
		IntDomain lubResult = lub.subtract( domain.glb() );

		return new BoundSetDomain(glbResult, lubResult);

	}

	/**
	 * It subtracts the elements of the set {min..max}.
	 * @param min the left bound of the set.
	 * @param max the right bound of the set.
	 * @return the domain after removing the int elements specified by the set.
	 * 
	 */
	public SetDomain subtract(int min, int max) {

		IntDomain lubResult = lub.subtract(min, max);
		IntDomain glbResult = glb.subtract(min, max);

		return new BoundSetDomain(glbResult, lubResult);

	}

	/**
	 * It subtracts the set {value}.
	 * FIXME, it does not subtract set {value}, it subtracts value from the set domain.
	 * @return the result of the subtraction.
	 */
	public SetDomain subtract(int value) {

		SetDomain domain = this.cloneLight();

		domain.lub().subtract(value);
		domain.glb().subtract(value);

		return domain;
	}	

	/**
        * It returns string description of the domain.
        */
       @Override
       public String toString() {

               assert checkInvariants() == null : checkInvariants() ;

               if(this.glb.eq(this.lub))
                   if (glb.singleton())
                       return "{" + glb.toString() + "}";
                   else
                       return glb.toString();
               else {
            	   
                   StringBuffer result = new StringBuffer("{");
                   
                   if (glb.singleton())
                	   result.append("{").append( glb.toString() ).append("}");
                   else
                	   result.append( glb.toString() );

                   result.append("..");
                   
                   if (lub.singleton())
                	   result.append("{").append( lub.toString() ).append("}");
                   else
                	   result.append( lub.toString() );

                   result.append("}[card=").append( cardinality ).append("]");
                   
                   return result.toString();
                   
               }
       }

	/**
	 * It computes union of the supplied domain with this domain.
	 * @param domain the domain for which the union is computed.
	 * @return the union of this domain with the supplied one.
	 */
	public SetDomain union(SetDomain domain) {

		assert domain.checkInvariants() == null : domain.checkInvariants() ;

		IntDomain glbResult = glb.intersect(domain.glb());
		IntDomain lubResult = lub.union(domain.lub());
		
		return new BoundSetDomain(glbResult, lubResult);
		
	}

	/**
	 * It computes union of this domain and the interval.
	 * @param min the left bound of the interval (inclusive).
	 * @param max the right bound of the interval (inclusive).
	 * @return the union of this domain and the interval.
	 */

	public SetDomain union(int min, int max) {

		// FIXME, why not max >= min? 
		assert max > min : "min value is larger than max value";
		
		IntDomain glbResult = glb.union(min, max);
		IntDomain lubResult = lub.union(min, max);
		
		return new BoundSetDomain(glbResult, lubResult);
		
	}

	/**
	 * It computes union of this domain and value. 
	 * 
	 * @param value it specifies the value which is being added.
	 * @return domain which is a union of this one and the value.
	 */
	public SetDomain union(int value) {

		IntDomain glbResult = glb.union(value);
		IntDomain lubResult = lub.union(value);
	
		return new BoundSetDomain(glbResult, lubResult);
	
	}

	/**
	 * It returns value enumeration of the domain values.
	 * @return valueEnumeration which can be used to enumerate the sets of this domain one by one.
	 */
	@Override
	public ValueEnumeration valueEnumeration() {
		
		return new SetDomainValueEnumeration(this);
	
	}

	/**
	 * @return It returns the information about the first invariant which does not hold or null otherwise. 
	 */
	public String checkInvariants() {
	
		if(!lub.contains(glb))
			return "Greatest lower bound is larger than least upper bound ";

		//Fine, all invariants hold.
		return null;

	}

	/**
	 * It adds if necessary an element to glb.
	 * @param level level at which the change is recorded.
	 * @param var set variable to which the change applies to.
	 * @param element the element which must be in glb.
	 */
	public void inGLB(int level, SetVar var, int element) {

		if (glb.contains(element))
			return;

		if (!lub.contains(element))
			throw Store.failException;

		if (stamp == level) {

			glb.unionAdapt(element);

			cardinality.intersectAdapt(glb.getSize(), lub.getSize());
			if (cardinality.isEmpty())
				throw Store.failException;

			if (cardinality.max() == glb.getSize()) {
				lub = glb;
				cardinality.intersectAdapt(glb.getSize(), glb.getSize());
			}

			if (singleton())
				var.domainHasChanged(SetDomain.GROUND);
			else
				var.domainHasChanged(SetDomain.GLB);		

		} else {

			assert stamp < level;

			BoundSetDomain result = new BoundSetDomain();
			IntDomain resultGLB = glb.union(element);
			IntDomain resultCardinality = cardinality.intersect(resultGLB.getSize(), lub.getSize());

			if (resultCardinality.isEmpty())
				throw Store.failException;

			result.glb = resultGLB;

			if (resultCardinality.max() == resultGLB.getSize()) {
				result.lub = resultGLB;
				resultCardinality.intersectAdapt(resultGLB.getSize(), resultGLB.getSize());
			}
			else
				result.lub = lub.cloneLight();

			result.cardinality = resultCardinality;
			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = level;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			var.domain = result;

			if (result.singleton())
				var.domainHasChanged(SetDomain.GROUND);
			else
				var.domainHasChanged(SetDomain.GLB);		

		}


	}

	/**
	 * It removes if necessary an element from lub.
	 * @param level level at which the change is recorded.
	 * @param var set variable to which the change applies to.
	 * @param element the element which can not be in lub.
	 */
	@Override
	public void inLUBComplement(int level, SetVar var, int element) {

		if (!lub.contains(element))
			return;

		if (glb.contains(element))
			throw Store.failException;

		if (stamp == level) {

			lub.subtractAdapt(element);

			cardinality.intersectAdapt(glb.getSize(), lub.getSize());
			if (cardinality.isEmpty())
				throw Store.failException;

			if (cardinality.min() == lub.getSize()) {
				glb = lub;
				cardinality.intersectAdapt(lub.getSize(), lub.getSize());
			}

			if (singleton())
				var.domainHasChanged(SetDomain.GROUND);		
			else
				var.domainHasChanged(SetDomain.LUB);		


		} else {

			assert stamp < level;

			IntDomain resultLUB = lub.subtract(element);
			IntDomain resultCardinality = cardinality.intersect(glb.getSize(), resultLUB.getSize());

			if (resultCardinality.isEmpty())
				throw Store.failException;

			BoundSetDomain result = new BoundSetDomain();
			result.lub = resultLUB;

			if (resultCardinality.min() == resultLUB.getSize()) {
				result.glb = resultLUB;
				resultCardinality.intersectAdapt(resultLUB.getSize(), resultLUB.getSize());
			}
			else
				result.glb = glb.cloneLight();

			result.cardinality = resultCardinality;

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = level;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			var.domain = result;

			if (result.singleton())
				var.domainHasChanged(SetDomain.GROUND);		
			else
				var.domainHasChanged(SetDomain.LUB);		

		}		

	}

	@Override
	public void inValue(int level, SetVar var, IntDomain set) {

		if (!set.contains(glb))
			throw Store.failException;

		if (!lub.contains(set))
			throw Store.failException;

		if (!cardinality.contains(set.getSize()))
			throw Store.failException;

		if (lub.eq(glb))
			return;

		if (stamp == level) {

			glb.unionAdapt(set);
			lub = glb;
			cardinality.intersectAdapt(glb.getSize(), glb.getSize());

		} else {

			assert stamp < level;

			// FIXME, allow specification of the sets in parts, so no unnecessary copying occur. 
			BoundSetDomain result = new BoundSetDomain(set, set);
			result.cardinality = new IntervalDomain(set.getSize(), set.getSize());

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = level;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			var.domain = result;

		}

		var.domainHasChanged(SetDomain.GROUND);		

	}	

	@Override
	public boolean singleton(Domain value) {

		if (!singleton())
			return false;

		if (value instanceof IntDomain) {
			return glb.eq( (IntDomain)value );
		}

		if (value instanceof BoundSetDomain) {

			BoundSetDomain input = (BoundSetDomain)value;
			if (!input.singleton())
				throw new IllegalArgumentException("The input parameter value is not a singleton domain.");

			return glb.eq(input.glb);

		}

		throw new IllegalArgumentException("Not recognized domain type for the input parameter value.");

	}

	@Override
	public void inLUB(int level, SetVar var, IntDomain intersect) {

		if (intersect.contains(lub))
			return;
		
		if (!intersect.contains(glb))
			throw Store.failException;

		if (stamp == level) {

			int event;
			
//			if (intersect.domainID() == IntDomain.SmallDenseDomainID && lub.domainID() == IntDomain.IntervalDomainID) {
//				IntDomain replacement = intersect.cloneLight();
//				event = replacement.intersectAdapt(lub);
//				lub = replacement;
//			}
//			else
				event = lub.intersectAdapt(intersect);

			if (event == Domain.NONE)
				return;
			else {

				cardinality.intersectAdapt(glb.getSize(), lub.getSize());

				if (cardinality.isEmpty())
					throw Store.failException;

				if (cardinality.min() == lub.getSize()) {
					glb = lub;
					cardinality.intersectAdapt(lub.getSize(), lub.getSize());
				}

				if (singleton())
					var.domainHasChanged(SetDomain.GROUND);
				else
					var.domainHasChanged(SetDomain.LUB);

			}

		}
		else {

			assert stamp < level;

			IntDomain resultLUB = lub.intersect(intersect);

			// This check was generalized and moved to the beginning of the function.
			// TODO, Check that early exit is ok. For some reason it is NOT ok, 
			// most likely a pruning bug in some other code in respect to cardinality part.
			// Cardinality part most likey fixed, some of the constraints maybe is missing
			// propagation and only forced call of consistency function below recovers
			// the lost pruning.
			//if (cardinality.min() < resultLUB.getSize() && resultLUB.eq(lub))
			//	return;

			IntDomain resultCardinality = cardinality.intersect(glb.getSize(), resultLUB.getSize());
			if (resultCardinality.isEmpty())
				throw Store.failException;

			// TODO, remove as early exit is moved higher. 
			//if (resultCardinality.min() < resultLUB.getSize() && resultLUB.eq(lub))
			//	return;
			
			BoundSetDomain result = new BoundSetDomain();

			if (resultCardinality.min() == resultLUB.getSize()) {
				result.glb = resultLUB;
				resultCardinality.intersectAdapt(resultLUB.getSize(), resultLUB.getSize());
			}
			else
				result.glb = glb.cloneLight();

			result.lub = resultLUB;
			result.cardinality = resultCardinality;

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = level;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			var.domain = result;

			if (result.singleton())
				var.domainHasChanged(SetDomain.GROUND);
			else
				var.domainHasChanged(SetDomain.LUB);

		}

	}

	
	/**
	 * It assigns a set variable to lub of its current domain. 
	 * 
	 * @param level level of the store at which the change takes place.
	 * 
	 * @param var variable for which the domain is changing. 
	 * 
	 */
	public void inValueLUB(int level, SetVar var) {

		if (lub.eq(glb))
			return;

		if (!cardinality.contains(lub.getSize()))
			throw Store.failException;		

		if (stamp == level) {

			glb = lub;
			cardinality.intersectAdapt(glb.getSize(), lub.getSize());

		} else {

			assert stamp < level;

			// FIXME, allow specification of the sets in parts, so no unnecessary copying occur. 
			BoundSetDomain result = new BoundSetDomain();
			result.lub = lub.cloneLight();
			result.glb = result.lub;

			result.cardinality = new IntervalDomain(lub.getSize(), lub.getSize());

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = level;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			var.domain = result;

		}

		var.domainHasChanged(SetDomain.GROUND);		

	}

	@Override
	public void inGLB(int level, SetVar var, IntDomain intersect) {

		if (glb.contains(intersect))
			return;

		if (!lub.contains(intersect))
			throw Store.failException;
		
		if (stamp == level) {

			int event = glb.unionAdapt(intersect);			

			if (event == Domain.NONE)
				return;
			else {

				cardinality.intersectAdapt(glb.getSize(), lub.getSize());
				if (cardinality.isEmpty())
					throw Store.failException;

				if (cardinality.max() == glb.getSize()) {
					lub = glb;
					cardinality.intersectAdapt(glb.getSize(), glb.getSize());
				}

				if (singleton())
					var.domainHasChanged(SetDomain.GROUND);
				else
					var.domainHasChanged(SetDomain.GLB);

			}

		}
		else {

			assert stamp < level;

			IntDomain resultGLB = glb.union(intersect);

			// TODO CRUCIAL, if resultGLB is equal current glb then nothing should happen and the function should return. Check that this addition is
			// correct.
			// Turn on the lines below after domains are stable to check for potential pruning bugs.
			//if (cardinality.max() > resultGLB.getSize() && resultGLB.eq(glb))
			//	return;

			IntDomain resultCardinality = cardinality.intersect(resultGLB.getSize(), lub.getSize());
			if (resultCardinality.isEmpty())
				throw Store.failException;

			BoundSetDomain result = new BoundSetDomain();
			result.glb = resultGLB;

			if (resultCardinality.max() == resultGLB.getSize()) {
				result.lub = resultGLB;
				resultCardinality.intersectAdapt(resultGLB.getSize(), resultGLB.getSize());
			}
			else
				result.lub = lub.cloneLight();

			result.cardinality = resultCardinality;

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = level;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			var.domain = result;

			if (result.singleton())
				var.domainHasChanged(SetDomain.GROUND);
			else
				var.domainHasChanged(SetDomain.GLB);

		}

	}

	/**
	 * It assigns a set variable to glb of its current domain. 
	 * 
	 * @param level level of the store at which the change takes place.
	 * 
	 * @param var variable for which the domain is changing. 
	 * 
	 */
	public void inValueGLB(int level, SetVar var) {

		if (lub.eq(glb))
			return;

		if (!cardinality.contains(glb.getSize()))
			throw Store.failException;		

		if (stamp == level) {

			lub = glb;
			cardinality.intersectAdapt(glb.getSize(), lub.getSize());

		} else {

			assert stamp < level;

			BoundSetDomain result = new BoundSetDomain();
			result.glb = glb.cloneLight();
			result.lub = result.glb;
			result.cardinality = new IntervalDomain(glb.getSize(), glb.getSize());

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = level;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			var.domain = result;

		}

		var.domainHasChanged(SetDomain.GROUND);		

	}

	@Override
	public void addDom(Interval i) {
		
		this.lub = this.lub.union( i.min, i.max );
		this.cardinality = new IntervalDomain(glb.getSize(), lub.getSize());

	}

	@Override
	public void inCardinality(int level, SetVar var, int min, int max) {

		// it is needed to make sure that this function is only executed when something is being changed.
		if (min <= cardinality.min() && cardinality.max() <= max)
			return;

		if (stamp == level) {

			IntDomain cardinality = var.domain.card();

			cardinality.intersectAdapt(min, max);

			if (var.domain.card().isEmpty())
				throw Store.failException;

			if (cardinality.max() == glb.getSize()) {
				this.inValue(level, var, glb);
				return;
			}
			
			if (cardinality.min() == lub.getSize()) {
				this.inValue(level, var, lub);
				return;
			}

		}
		else {

			assert stamp < level;

			IntDomain resultCardinality = cardinality.intersect(min, max);

			if (resultCardinality.isEmpty())
				throw Store.failException;

			if (resultCardinality.max() == glb.getSize()) {
				this.inValue(level, var, glb);
				return;
			}
			if (resultCardinality.min() == lub.getSize()) {
				this.inValue(level, var, lub);
				return;
			}

			BoundSetDomain result = new BoundSetDomain(glb, lub);
			result.cardinality = resultCardinality;

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = level;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			var.domain = result;

		}

		var.domainHasChanged(SetDomain.CARDINALITY);

	}

}
