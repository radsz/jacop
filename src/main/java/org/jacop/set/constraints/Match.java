/**
 *  Match.java 
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
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * This constraint matches the elements of the given set variable
 * onto a list of integer variables. 
 * 
 * @author Radoslaw Szymanek, Krzysztof Kuchcinski, and Robert Åkemalm
 * @version 4.2
 */

public class Match extends Constraint {

	static int idNumber = 1;

	/**
	 * It specifies a set variable whose values are being matched against integer variables
	 * from the list. 
	 */
	public SetVar a;
	
	/**
	 * It specifies the list of integer variables which value is being matched against
	 * elements from a set variable a.
	 */
	public IntVar[] list;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"a", "list"};

	/**
	 * It constructs a match constraint to connect the value of set variable a
	 * to the values of integer variables provided in the list. 
	 * 
	 * @param a set variable that is restricted to be equal to a set created from values specified by integer variables form the list. 
	 * @param list of integer variables that is restricted to have the same elements as set variable a.
	 */

	public Match(SetVar a, IntVar[] list) {

		assert (a != null) : "Variable a is null";
		for (int i = 0; i < list.length; i++)
			assert (list[i] != null) : i + "-th element of the list is null.";

		this.numberId = idNumber++;
		this.numberArgs = list.length + 1;
		this.a = a;
		this.list = new IntVar[list.length]; 
		
		System.arraycopy(list, 0, this.list, 0, list.length);

	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(list.length +1);

		variables.add(a);
		for(Var fdv : list)
			variables.add(fdv);

		return variables;
	}

	@Override
	public void consistency(Store store) {
	
		/**
		 * It specifies the consistency rules for constraint 
		 * match(list, a) where list is a list of intVar and a is a setVar. 
		 * 
		 * list is lexicographically ordered elements of a. 
		 * 
		 * [a, b, c, e, f] = {a, b, c, e, f}
		 * 
		 * #A = list.length
		 * 
		 * each element el in A.glb must occurr in one of the intvar in list. 
		 * elPos is lexicographical position of el in A.glb
		 * 
		 * element el can only occur within an interval of intvars list[elPos]..list[list.length - (#A.glb-elPos)]
		 * 
		 * every element elU in A.lub that is not in A.glb can if added to glb will end up at position posElU
		 * and for this element we can also say that it can only occur in list[posElU]..list[list.length - (1+#A.glb-posElU)]
		 * 
		 * for all l[i], D(l[i]) must be in A.lub
		 * 
		 * A.lub = A.lub /\ ( \/ D(i) ). 
		 * 
		 */
	
		a.domain.inCardinality(store.level, a, list.length, list.length);
		
		if(a.domain.glb().getSize() == list.length) {

			ValueEnumeration ve = a.domain.glb().valueEnumeration();
			int el;
			for(int i = 0 ; i < list.length ; i++){
				el = ve.nextElement();
				list[i].domain.in(store.level, list[i], el, el);
			}
			a.domain.inLUB(store.level, a, a.domain.glb());
			
		} else if(a.domain.lub().getSize() == list.length) {

			ValueEnumeration ve = a.domain.lub().valueEnumeration();
			int el;
			for(int i = 0 ; i < list.length ; i++){
				el = ve.nextElement();
				list[i].domain.in(store.level, list[i], el, el);
			}
			a.domain.inGLB(store.level, a, a.domain.lub());
			
		} else {

			IntDomain glbA = a.domain.glb();
			IntDomain lubA = a.domain.lub();
			
			int sizeOfaGLB = glbA.getSize();
			int sizeOfaLUB = lubA.getSize();
			
			// glbA, lubA => list[i]
			for (int i = 0; i < list.length; i++) {
			
				list[i].domain.in(store.level, list[i], lubA);
				
				int minValue = lubA.getElementAt( i );
				
				if (i >= list.length - sizeOfaGLB) {
					// -1 since indexing of arrays starts from 0.
					int minValueFromGLB = glbA.getElementAt( sizeOfaGLB - list.length + i );
					if (minValueFromGLB > minValue)
						minValue = minValueFromGLB;
				}

				list[i].domain.inMin(store.level, list[i], minValue);

				int maxValue = lubA.getElementAt( sizeOfaLUB - list.length + i );
				
				if (i < sizeOfaGLB) {
					int maxValueFromGLB = glbA.getElementAt ( i );
					if (maxValueFromGLB < maxValue)
						maxValue = maxValueFromGLB;
				}
				
				list[i].domain.inMax(store.level, list[i], maxValue);
				
			}

			IntDomain lubFromList = list[0].domain.cloneLight();
			for (int i = 0; i < list.length; i++) {
				if (list[i].singleton())
					a.domain.inGLB(store.level, a, list[i].value());
				if (i > 0)
					lubFromList.unionAdapt(list[i].domain);
			}
			a.domain.inLUB(store.level, a, lubFromList);			

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
		
		if (var == a)
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
		a.putModelConstraint(this, getConsistencyPruningEvent(a));
		for(Var fdv : list)
		    fdv.putModelConstraint(this, getConsistencyPruningEvent(fdv));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeConstraint() {
		a.removeConstraint(this);
		for(Var fdv :list)
			fdv.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		
		if(a.domain.glb().getSize() == list.length && a.singleton()) {
			
			ValueEnumeration ve = a.domain.glb().valueEnumeration();
			
			for(int i = 0 ; i < list.length ; i++) {
				if(!list[i].singleton())
					return false;
				if(ve.nextElement() != list[i].min())
					return false;
			}
			
			return true;
			
		}
		
		return false;
		
	}



	@Override
	public String toString() {
		
		// FIXME, use StringBuffer, or automatic generation of String description.
		String ret = id() + " : Match(" + a + ", [ ";
		for(Var fdv : list)
			ret += fdv + " ";
		ret +="] )";
		return ret;
		
	}

	@Override
	public void increaseWeight() {
		
		if (increaseWeight) {
			a.weight++;
			for(Var fdv : list)
				fdv.weight++;
		}
		
	}	

}
