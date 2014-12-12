/**
 *  VarHandler.java 
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

import java.util.List;

import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * 
 * Common interface to all objects that can handle one or more variables of the
 * network flow constraint.
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 */

public interface VarHandler {

	/**
	 * @return the list of variables handled by this handler
	 */
	public abstract List<IntVar> listVariables();

	/**
	 * Retrieves the consistency pruning event of a handler variable that causes
	 * the handler to be reevaluated. For instance, X- and W-variables will
	 * listen to BOUND events while S-variables typically consider ANY events.
	 * 
	 * @param variable a handler variable
	 * @return the pruning event which causes reevaluation of the handler
	 */
	public abstract int getPruningEvent(Var variable);

	/**
	 * Informs the handler that one of its variable has changed and asks the
	 * handler to update the state of the network accordingly.
	 * 
	 * @param variable the variable that changed
	 * @param network the network
	 */
	public abstract void processEvent(IntVar variable, MutableNetwork network);

}
