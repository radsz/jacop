/**
 *  SetDomainValueEnumeration.java 
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

import org.jacop.core.IntDomain;
import org.jacop.core.ValueEnumeration;

/**
 * Defines a methods for enumerating values contained in the SetDomain.
 * 
 * @author Robert Åkemalm
 * @version 4.2
 */

public class SetDomainValueEnumeration extends ValueEnumeration {

	IntDomain current;
	IntDomain min;
	IntDomain max;
	int maxLevel;
	int currentLevel;
	int pascalPlace;

	SetDomain domain;

	/**
	 * @param dom It specifies the SetDomain for which enumeration of sets is performed.
	 */
	public SetDomainValueEnumeration(SetDomain dom) {
		min = dom.glb();
		current = dom.glb();
		max = dom.lub();
		domain = dom;
		currentLevel = 0;
		maxLevel = max.getSize() - min.getSize();
		pascalPlace = 1;
	}

	@Override
	public boolean hasMoreElements() {
		if(currentLevel == maxLevel+1 )
			return false;
		return true;
	}

	/**
	 * The function nextElement has to return a Set. Use nextSetElement instead.
	 */
	@Override
	public int nextElement() {
		throw new RuntimeException("This function should not be used, use nextSetElement instead.");
	}

	/**
	 * Returns the next element in the SetDomain. 
	 * @return the next element in the SetDomain.
	 */

	public IntDomain nextSetElement() {
		IntDomain ret = getPascal(currentLevel,pascalPlace);
		if(pascalPlace >= this.getMaxPascal(currentLevel)){
			++currentLevel;
			pascalPlace = 0;
		}
		++pascalPlace;
		return ret;
	}

	@Override
	public void domainHasChanged() {
		min = domain.glb();
		current = domain.glb();
		max = domain.lub();
		currentLevel = 0;
		maxLevel = max.getSize() - min.getSize();
		pascalPlace = 0;
	}

	/**
	 * The number of elements at each level is described by Pascal's-triangle.
	 * Example: domain = {{}..{1..3}
	 * 	glb.size = 0
	 * 	lub.size = 3
	 * the level(pascalLevel) in Pascal's-triangle: level = 3-0 (lub.size-glb.size)
	 * This level(pascalLevel) in Pascal's-triangle is 1 3 3 1
	 * And we get the elements:
	 * level 0 : {}
	 * level 1 : {1}, {2}, {3}
	 * level 2 : {1,2}, {1,3}, {2,3}
	 * level 3 : {1,2,3}
	 * So getPascal(2,2) returns the Set {1,3} 
	 * 
	 * occLevel = The level in Pascal's triangle that describes how many times the first
	 * 			value occurs.
	 * 
	 * occPos = the position in Pascal's triangle on row occLevel that describes how many
	 * 			times the first value occurs
	 * 
	 *  occ = the number of times the first value occurs.
	 *  
	 * @param level = Number of element from the ground set(lub\glb) that should be added
	 * @param place = The position in this level for the wanted element
	 * @return domain that specifies Pascal triangle element at positions (level, place)
	 */
	private IntDomain getPascal(int level,int place) {
		if(level == this.maxLevel)
			return this.max.cloneLight();

		IntDomain ret = this.min.cloneLight();
		if(level == 0)
			return ret;
		int maxPlace = this.getMaxPascal(level);
		assert (place <= maxPlace);
		int occLevel = this.maxLevel-1;
		int occPlace = level;
		int occ = this.getPascalNbr(occLevel, occPlace);
		ValueEnumeration ve = this.max.subtract(this.min).valueEnumeration();
		int added = 0;
		int v;
		while(added<level){
			v = ve.nextElement();
			if(place > occ){
				place -= occ;
				occLevel -= 1;
				occ = this.getPascalNbr(occLevel, occPlace);
			}else{
				ret.unionAdapt(v);
				++added;
				occLevel -= 1;
				occPlace -= 1;
				occ = this.getPascalNbr(occLevel, occPlace);
			}
		}
		return ret;
	}

	/**
	 * Returns the maximum place number for an element in this level
	 * @param level
	 * @return the maximum place number for an element in this level
	 */
	private int getMaxPascal(int level){
		return getPascalNbr(this.maxLevel,level+1);
	}

	/**
	 * Returns the value of a specific element in Pascal's triangle. 
	 * @param level The level in Pascal's triangle.
	 * @param place The position in this level of Pascal's triangle.
	 * @return The element on this position in Pascal's triangle.
	 */
	private int getPascalNbr(int level, int place) {
		if(level < 1 || place < 1)
			return 1;
		if(place == (level + 1) || place == 1)
			return 1;
		else{
			return (getPascalNbr(level-1, place -1) + getPascalNbr(level-1, place));
		}
	}

}
