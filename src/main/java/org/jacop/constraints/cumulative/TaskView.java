/*
 * TaskView.java
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

package org.jacop.constraints.cumulative;

import org.jacop.core.IntVar;

/**
 * Represents tasks for cumulative constraint
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

abstract class TaskView extends Task {

    TaskView(IntVar start, IntVar dur, IntVar res) {
        super(start, dur, res);
    }

    abstract int lct();

    abstract int ect();

    abstract int est();

    abstract int lst();

    abstract long env(long C);

    abstract void updateEdgeFind(int storeLevel, int upd);

    abstract void updateNotFirstNotLast(int storeLevel, int upd);

    abstract void updateDetectable(int storeLevel, int est);

    abstract boolean exists();

    abstract boolean maxNonZero();
}
