/**
 *  SumWeightedSet.java 
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
import java.util.HashMap;

import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * 
 * It computes a weighted sum of the elements in the domain of the given set variable. 
 * The sum must be equal to the specified sum variable. 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class SumWeightedSet extends Constraint {

	static int idNumber = 1;

	/**
	 * A set variable a whose elements contribute with their weight to the sum. 
	 */
	public SetVar a;

	/**
	 * It specifies the list of allowed elements and helps to connect the weight
	 * to the element. 
	 */
	public int[] elements;

	/**
	 * It specifies a weight for every element of the allowed element in the
	 * domain of set variable a.
	 */
	public int[] weights;
	
	/**
	 * Integer variable containing the total weight of all elements within a set variable a.
	 */
	public IntVar totalWeight;

	/**
	 * It specifies if the costs of elements are increasing given the lexical order of the elements. 
	 */
	boolean increasingCosts;
	
	/**
	 * It provides a quick access to the weights of given elements of the set.
	 */
	HashMap<Integer,Integer> elementWeights;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"a", "elements", "weights", "totalWeight"};

	/**
	 * It constructs a weighted set sum constraint. 
	 *    
	 * @param a a set variable for which the weighted sum of its element is computed.
	 * @param elements it specifies the elements which are allowed and for which the weight is specified.
	 * @param weights the weight for each element present in a.lub(). 
	 * @param totalWeight an integer variable equal to the total weight of the elements in set variable a.
	 */
	public SumWeightedSet(SetVar a, int[] elements, int[] weights, IntVar totalWeight) {
		
		assert (weights != null) : "This constructor does not accept empty arrays for weights.";
		assert (weights.length == elements.length) : "Length of elements does not equal length of weights array.";
		assert (a != null) : "Variable a is null";
		assert (totalWeight != null) : "Variable totalWeight is null";
		
		this.numberId = idNumber++;
		this.numberArgs = 2;
		
		this.totalWeight = totalWeight;
		this.a = a;
		this.weights = new int[weights.length];
		System.arraycopy(weights, 0, this.weights, 0, weights.length);
		this.elements = new int[elements.length];
		System.arraycopy(elements, 0, this.elements, 0, elements.length);
		
		this.increasingCosts = true;
		for (int i = 0; i < weights.length - 1 && this.increasingCosts; i++)
			if (weights[i] > weights[i+1])
				this.increasingCosts = false;
		
		elementWeights = new HashMap<Integer,Integer>(weights.length);
		ValueEnumeration enumer = a.domain.lub().valueEnumeration();
		int i = 0;

		while(enumer.hasMoreElements())
			elementWeights.put(enumer.nextElement(), weights[i++]);

	}

	/**
	 * It constructs a weighted set sum constraint. This constructor assumes that every element
	 * within a set variable has a weight equal to its value.
	 *  
	 * @param a set variable being used in weighted set constraint.  
	 * @param totalWeight integer variable containing information about total weight of the elements in set variable a.
	 */
	public SumWeightedSet(SetVar a, IntVar totalWeight) {
		
		this(a, a.domain.lub().toIntArray(), a.domain.lub().toIntArray(), totalWeight);		

	}

	/**
	 * It constructs a weighted set sum constraint. This constructor assumes that every element
	 * within a set variable has a weight equal to its value.
	 *  
	 * @param a set variable being used in weighted set constraint.  
	 * @param weights it specifies a weight for each possible element of a set variable.
	 * @param totalWeight integer variable containing information about total weight of the elements in set variable a.
	 */
	public SumWeightedSet(SetVar a, int[] weights, IntVar totalWeight) {
		
		this(a, a.domain.lub().toIntArray(), weights, totalWeight);		

	}


	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(2);

		variables.add(totalWeight);
		variables.add(a);

		return variables;
	}

	// FIXME, TODO, Analyse all set constraints fixpoints.
	
	// FIXME, TODO, implement also cardinality reasoning for increasingCosts = false.
	// For example a simple approach could sort weights and ignore elements being removed from lub. 
	// More elaborate approach, sort weights, for each weight keep an element responsible for this weight. 
	// before considering weight in any calculation check if that element is still in the lub. 
	@Override
	public void consistency(Store store) {
		
		/**
		 * It specifies the consistency rules for this constraint. 
		 * 
		 * totalWeight.inMin( glb.weight )
		 * totalWeight.inMax( lub.weight )
		 * 
		 * if any element el in lub \ glb has weight such that 
		 * glb.weight + el.weight > totalweight.max() then el is removed from lub
		 * 
		 * if any element el in lub \ glb has weight such that
		 * lub.weight - el.weight < totalweight.min() then el is included in glb.
		 * 
		 * If cardinality specifies that some additional elements must be in glb
		 * then take the smallest weights from potential elements and add to minimalWeight. 
		 * 
		 * Similarly, if cardinality specifies that some elements from lub can not be 
		 * taken then reduce the maximal potential weight by the smallest weight of elements
		 * from potential elements.
		 * 
		 */
		
		while (true) {

			int glbSum = 0;
			int lubSum = 0;

			IntDomain glbA = a.domain.glb();		
			IntDomain lubA = a.domain.lub();
			IntDomain potentialEl = lubA.subtract(glbA);

			ValueEnumeration enumer = glbA.valueEnumeration();
			while(enumer.hasMoreElements())
				glbSum += elementWeights.get(enumer.nextElement());

			lubSum = glbSum;

			int noOfRequiredEl = a.domain.card().min() - glbA.getSize();
			int weightOfLastRequiredEl = 0;

			if (increasingCosts)
				if (noOfRequiredEl > 0) {
					enumer = potentialEl.valueEnumeration();
					while (noOfRequiredEl > 1) {
						glbSum += elementWeights.get( enumer.nextElement() );
						noOfRequiredEl--;
					}
					weightOfLastRequiredEl = elementWeights.get( enumer.nextElement() );
				}		

			enumer = potentialEl.valueEnumeration();

			Integer el, weight;
			boolean change = false;
			while(enumer.hasMoreElements()){

				el = enumer.nextElement();
				weight = elementWeights.get(el);

				if(totalWeight.max() < glbSum + weight) {
					a.domain.inLUBComplement(store.level, a, el);
					change = true;
				}
			}
			
			// inLUB above can change GLB due to cardinality constraints. Need to recompute. 
			if (change)
				continue;

			int noOfSkippedEl = a.domain.lub().getSize() - a.domain.card().max();
			int weightOfLastSkippedItem = 0;

			enumer = potentialEl.valueEnumeration();

			while(enumer.hasMoreElements()){

				el = enumer.nextElement();
				weight = elementWeights.get(el);

				if (increasingCosts)
					if (noOfSkippedEl == 0)
						lubSum += weight;
					else {
						if (noOfSkippedEl == 1)
							weightOfLastSkippedItem = weight;
						noOfSkippedEl--;
					}
				else
					lubSum += weight;
			}		

			enumer = potentialEl.valueEnumeration();
			while(enumer.hasMoreElements()){

				el = enumer.nextElement();
				weight = elementWeights.get(el);

				if(totalWeight.min() > lubSum + weightOfLastSkippedItem - weight) {
					a.domain.inGLB(store.level, a, el);
					change = true;
				}
			}

			// inGLB above can change LUB due to cardinality constraints. Need to recompute.
			if (change)
				continue;
			
			totalWeight.domain.in(store.level, totalWeight, glbSum + weightOfLastRequiredEl, lubSum + weightOfLastRequiredEl);

			return;
		}

	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		if (var == this.a)
			return SetDomain.ANY;
		else
			return IntDomain.ANY;
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
		totalWeight.putModelConstraint(this, getConsistencyPruningEvent(totalWeight));
		a.putModelConstraint(this, getConsistencyPruningEvent(a));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeConstraint() {
		totalWeight.removeConstraint(this);
		a.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {

		if(!totalWeight.singleton())
			return false;
		
		if( a.singleton() ) {
			ValueEnumeration enumer = a.domain.glb().valueEnumeration();
			int sum = 0;
			while(enumer.hasMoreElements())
				sum += elementWeights.get(enumer.nextElement());
			return totalWeight.value() == sum;
		}
		else
			return false;
			
	}

	@Override
	public String toString() {
		// FIXME, use StringBuffer or automatically generated toString function.
		String ret = id() + " : SumWeightedSet(" + a + ", < ";
		Integer weight;
		for ( Integer el : elementWeights.keySet()){
			weight = elementWeights.get(el);
			ret += "<"+el+","+weight+"> ";
		}
		ret +=">, ";
		if(totalWeight.singleton())
			return ret + totalWeight.min()+" )";
		else
			return ret + totalWeight.dom()+" )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			a.weight++;
			totalWeight.weight++;
		}
	}	

}
