/**
 *  MutableDomain.java 
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

/**
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */
public class MutableDomain implements MutableVar {

	/**
	 * It specifies if debugging info should be printed out.
	 */
	public final static boolean debug = false;
	
	int index;

	Store store;

	MutableDomainValue value = null;

	/**
	 * @param store store in which the mutable domain is created.
	 */
	public MutableDomain(Store store) {
		MutableDomainValue val = new MutableDomainValue(IntervalDomain.emptyDomain);
		value = val;
		index = store.putMutableVar(this);
		this.store = store;
	}

	/**
	 * @param store store in which the mutable domain is created.
	 * @param domain specifies the domain used to create mutable domain.
	 */
	public MutableDomain(Store store, IntDomain domain) {
		MutableDomainValue val = new MutableDomainValue();
		val.domain = domain;
		value = val;
		index = store.putMutableVar(this);
		this.store = store;
	}

	int index() {
		return index;
	}

	public MutableVarValue previous() {
		return value.previousMutableDomainVariableValue;
	}

	public void removeLevel(int removeLevel) {
		if (value.stamp == removeLevel) {
			value = value.previousMutableDomainVariableValue;
		}
	}

	public void setCurrent(MutableVarValue o) {
		value = (MutableDomainValue) o;
	}

	int stamp() {
		return value.stamp;
	}

	@Override
	public String toString() {
		
		StringBuffer buffer = new StringBuffer("MutableVar[");
		buffer.append( (index + 1) ).append("] = ");
		buffer.append( value );
		return buffer.toString();
		
	}

	public void update(MutableVarValue val) {

		if (value.stamp == store.level) {
			
			if (debug)
				System.out.print("1. Level: " + store.level + ", IN " + value + ", New " + val);
			
			value.setValue(((MutableDomainValue) val).domain);
			
			if (debug)
				System.out.println(", OUT "+ value);
			
		} else if (value.stamp < store.level) {
			if (debug) 
				System.out.print("2. Level: " + store.level + ", IN " + this + ", New " + val);

			val.setStamp(store.level);
			val.setPrevious(value);
			
			value = (MutableDomainValue) val;

			if (debug) 
				System.out.println("\n=> OUT "+ this + "\nOLD " + value().previous());
		}
	}

	public MutableVarValue value() {
		return value;
	}
}
