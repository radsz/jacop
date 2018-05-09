/*
 * Task.java
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

package org.jacop.constraints;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;

/**
 * Represents tasks for cumulative constraint
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

class Task {

    final IntVar start, dur, res;

    Task(IntVar start, IntVar duration, IntVar resourceUsage) {
        this.start = start;
        this.dur = duration;
        this.res = resourceUsage;
    }

    long areaMax() {
        return dur.max() * res.max();
    }

    long areaMin() {
        return dur.min() * res.min();
    }

    IntDomain compl() {
        IntDomain sDom = start.dom();
        IntDomain dDom = dur.dom();
        return new IntervalDomain(sDom.min() + dDom.min(), sDom.max() + dDom.max());
    }

    IntDomain completion() {
        IntDomain sDom = start.dom();
        int dDomMin = dur.dom().min();
        return new IntervalDomain(sDom.min() + dDomMin, sDom.max() + dDomMin);
    }

    IntVar dur() {
        return dur;
    }

    int ect() {
        return start.min() + dur.min();
    }

    int est() {
        return start.min();
    }

    int lastCT() {
        return start.max() + dur.max();
    }

    int lct() {
        return start.max() + dur.min();
    }

    int lst() {
        return start.max();
    }

    boolean minUse(IntTask t) {
        int lst, ect;
        IntDomain sDom = start.dom();

        lst = sDom.max();
        ect = sDom.min() + dur.min();
        if (lst < ect) {
            t.start = lst;
            t.stop = ect;
            return true;
        } else
            return false;
    }

    IntVar res() {
        return res;
    }

    IntVar start() {
        return start;
    }

    boolean nonZeroTask() {
	return dur.min() > 0 && res.min() > 0;
    }

    @Override public String toString() {
        return "[" + start + ", " + dur + ", " + res + "]";
    }

}
