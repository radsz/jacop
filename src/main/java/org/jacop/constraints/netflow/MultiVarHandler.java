/**
 *  MultiVarHandler.java 
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


package org.jacop.constraints.netflow;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class MultiVarHandler implements VarHandler {

	private final IntVar variable;
	private final ArrayList<VarHandler> handlers;
	
	
	public MultiVarHandler(IntVar variable, VarHandler ... handlers) {
		this.variable = variable;
		this.handlers = new ArrayList<VarHandler>(Arrays.asList(handlers));
	}
	
	public void add(VarHandler handler) {
		assert(handler.listVariables().contains(variable));
		handlers.add(handler);
	}
	
	
	public int getPruningEvent(Var variable) {
		assert(this.variable == variable);
		int max = IntDomain.GROUND;
		for (VarHandler handler : handlers) {
			int event = handler.getPruningEvent(variable);
			if (max < event) {
				max = event;				
			}
		}
		return max;
	}

	
	public List<IntVar> listVariables() {
		return Collections.singletonList(variable);
	}

	
	public void processEvent(IntVar variable, MutableNetwork network) {
		assert(this.variable == variable);
		for (VarHandler handler : handlers)
			handler.processEvent(variable, network);
	}

}
