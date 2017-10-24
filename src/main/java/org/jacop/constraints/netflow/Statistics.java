/*
 * Statistics.java
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

package org.jacop.constraints.netflow;

/**
 *
 * This class stores all the statistics gather during the execution of the network flow constraint. 
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.5
 *
 */

public class Statistics extends StatisticsBase {

    public final StatisticsBase NVARS = new StatisticsBase();
    public final StatisticsBase XVARS = new StatisticsBase();
    public final StatisticsBase WVARS = new StatisticsBase();
    public final StatisticsBase SVARS = new StatisticsBase();

    public String toString() {

        StringBuilder str = new StringBuilder();

        str.append("# consistency calls      : ");
        str.append(consistencyCalls);

        str.append("\n# consistency iterations : ");
        str.append(consistencyIterations);
        str.append("\t(avg ");
        str.append(StatisticsBase.DF.format((double) consistencyIterations / consistencyCalls));
        str.append(")");

        if (NVARS.arcsExamined > 0) {
            str.append("\nFor X-variables GAC-pruning (node with degree <= 2)\n");
            NVARS.toString(str);
        }
        if (XVARS.arcsExamined > 0) {
            str.append("\nFor X-variables\n");
            XVARS.toString(str);
        }
        if (WVARS.arcsExamined > 0) {
            str.append("\nFor W-variables\n");
            WVARS.toString(str);
        }
        if (SVARS.arcsExamined > 0) {
            str.append("\nFor S-variables\n");
            SVARS.toString(str);
        }
        return str.toString();
    }

}
