/**
 *  MutableDomainValue.java
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

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class MutableDomainValue implements MutableVarValue { private static Logger logger = LoggerFactory.getLogger(MutableDomainValue.class);

	/**
	 * It stores the value of the mutable domain.
	 */
	public Domain domain;

	MutableDomainValue previousMutableDomainVariableValue = null;

	int stamp = 0;

	MutableDomainValue() {
	}

	/**
	 * @param domain specifies domain stored by a mutable domain.
	 */
	public MutableDomainValue(Domain domain) {
		this.domain = domain;
	}

	@Override
	public Object clone() {

		MutableDomainValue val = new MutableDomainValue(domain.clone());
		val.stamp = stamp;
		val.previousMutableDomainVariableValue = previousMutableDomainVariableValue;
		return val;
	}

	public MutableVarValue previous() {
		return previousMutableDomainVariableValue;
	}

	public void setPrevious(MutableVarValue nn) {
		previousMutableDomainVariableValue = (MutableDomainValue) nn;
	}

	public void setStamp(int stamp) {
		this.stamp = stamp;
	}

	void setValue(Domain domain) {
		this.domain = domain;
	}

	public int stamp() {
		return stamp;
	}

	@Override
	public String toString() {
		return "[" + domain + "]";
	}

}
