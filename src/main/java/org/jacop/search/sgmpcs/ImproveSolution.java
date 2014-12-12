/**
 *  ImproveSolution.java 
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

package org.jacop.search.sgmpcs;

import org.jacop.core.Var;

/**
 * Defines an interface for defining different methods for selecting next search
 * decision to be taken. The search decision called choice point will be first
 * enforced and later upon backtrack a negation of that search decision will be
 * enforced.
 * 
 * @author krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of the variable for which choice point is being created.
 */

public interface ImproveSolution<T extends Var> {

    public boolean searchFromEmptySolution(int failLimit);

    public boolean searchFromEliteSolution(int[] solution, int failLimit);

    public int getCurrentCost();

    public int[] getSolution();

    public int getNumberFails();

    public int getFailLimit();

    public void setPrintInfo(boolean p);

    public void setTimeOut(long timeOut);

}
