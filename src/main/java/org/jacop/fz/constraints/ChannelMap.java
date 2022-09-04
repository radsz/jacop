/*
 * ChannelMap.java
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

package org.jacop.fz.constraints;

import org.jacop.core.*;
import java.util.Map;
import java.util.Set;
import java.util.HashMap;

/**
 * It collects all int_eq_(reif|imp) constraint to create Channel(Reif|Imply)
 * constraints, if possible.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */


class ChannelMap {

    Map<IntVar, Map<Integer, IntVar>> cs = new HashMap<>();

    int minSize = 1;

    Support support;

    public ChannelMap(Support support) {
        this.support = support;
    }

    public void add(IntVar x, int v, IntVar b) {
        Map<Integer, IntVar> map = cs.get(x);

        if (map != null)
            if (map.get(v) != null) {
                support.delayedConstraints.add(new org.jacop.constraints.XeqY(map.get(v), b));
            } else {
                map.put(v, b);
                cs.put(x, map);
            }
        else {
            map = new HashMap<>();
            map.put(v, b);
            cs.put(x, map);
        }
    }

    public int size(IntVar v) {
        Map<Integer, IntVar> m = cs.get(v);

        if (m != null)
            return m.size();
        else
            return 0;
    }

    public String toString() {

        StringBuilder result = new StringBuilder();

        Set<Map.Entry<IntVar, Map<Integer,IntVar>>> entries = cs.entrySet();

        for (Map.Entry<IntVar, Map<Integer,IntVar>> e : entries) {
            IntVar var = e.getKey();
            Map<Integer,IntVar> vb = e.getValue();
            Set<Map.Entry<Integer,IntVar>> es = vb.entrySet();

            result.append(var + "[");

            for (Map.Entry<Integer,IntVar> ei : es) {
                int val = ei.getKey();
                IntVar bb = ei.getValue();

                result.append("[" + val + ", " + bb + "]");
            }
        }
        result.append("]");
        return result.toString();
    }
}
