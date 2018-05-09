/*
 * MutableVarValue.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.core;

/**
 * Standard mutable variable's value definition
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public interface MutableVarValue {

    /**
     * It clones the value of mutable variable. It includes the stamp, pointer
     * to earlier value, and current value of variable.
     * @return clone of the mutable variable value.
     */
    Object clone();

    /**
     * It returns the earlier value of mutable variable.
     * @return earlier value of mutable variable.
     */
    MutableVarValue previous();

    /**
     * It replaces the earlier value of a mutable variable with value passed as
     * parameter.
     * @param o the previous value for this mutable variable.
     */
    void setPrevious(MutableVarValue o);

    /**
     * It sets the stamp of value of mutable variable.
     * @param stamp the new stamp of value of mutable variable
     */
    void setStamp(int stamp);

    /**
     * It returns the stamp value of value of mutable variable.
     * @return the current stamp of value of mutable variable.
     */
    int stamp();

    /**
     * It returns string representation of the current value of mutable
     * variable.
     */
    String toString();
}
