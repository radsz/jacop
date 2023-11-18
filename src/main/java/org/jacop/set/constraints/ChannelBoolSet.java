/*
 * ChannelBoolSet.java
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

package org.jacop.set.constraints;

import org.jacop.constraints.Constraint;
import org.jacop.core.*;
import org.jacop.set.core.*;
import org.jacop.api.SatisfiedPresent;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.Arrays;
import java.util.stream.Stream;

/**
 * Channel constraint reqires the array of Booleans b to be a
 * representation of the set s: i in s {@literal <->} b[i]. Indexes start form 0,
 * both for Boolean variables, by default. To define other starting
 * index use offset definitions.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */


public class ChannelBoolSet extends Constraint implements SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    IntVar[] b;
    SetVar s;
    int n;
    int offset;

    boolean firstConsistencyCheck = true;

    /**
     * It constructs a Channel constraint.
     *
     * @param b array of Boolean variables.
     * @param s set variable.
     * @param offset offset for Boolean variables array.
     */
    public ChannelBoolSet(IntVar[] b, SetVar s, int offset) {

        checkInputForNullness(new String[] {"b"}, new Object[] {b});

        numberId = idNumber.incrementAndGet();

        this.b = b;
        n = b.length;
        for (int i = 0; i < n; i++) {
            if (b[i].min() < 0 || b[i].max() > 1)
                throw new RuntimeException("Error; prameters in array of ChannelBoolSet must be in interval 0..1");
        }
        this.s = s;
        this.offset = offset;

        setScope(Stream.concat(Arrays.stream(b), Stream.of(s)));
    }

    /**
     * It constructs a Channel constraint.
     *
     * @param b array of Boolean variables.
     * @param s set variable.
     */
    public ChannelBoolSet(IntVar[] b, SetVar s) {
        this(b, s, 0);        
    }

    @Override public void consistency(Store store) {

        if (firstConsistencyCheck) {
            s.domain.inLUB(store.level, s,
                           new IntervalDomain(offset, n - 1 + offset));
            
            firstConsistencyCheck = false;
        }

        // check Boolean variables
        IntDomain ub = new IntervalDomain(5);
        IntDomain lb = new IntervalDomain(5);
        for (int i = 0; i < n; i++) {
            if (b[i].max() != 0)
                ub.unionAdapt(i + offset);
            if (b[i].singleton(1))
                lb.unionAdapt(i + offset);
        }
        s.domain.inLUB(store.level, s, ub);
        s.domain.inGLB(store.level, s, lb);

        // check set variable's GLB
        IntDomain glb = s.dom().glb();
        for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements(); ) {
            int i = e.nextElement();
            b[i - offset].domain.in(store.level, b[i - offset], 1, 1);
        }
    }

    @Override public boolean satisfied() {
        if (!allGround())
            return false;

        for (int i = 0; i < n; i++) {
            if (b[i].singleton(0) && s.dom().glb().contains(i + offset)) {
                return false;
            }
            if (b[i].singleton(1) && !s.dom().glb().contains(i + offset)) {
                return false;
            }
        }

        return true;
    }

    boolean allGround() {
        for (int i = 0; i < n; i++) {
            if (!b[i].singleton())
                return false;
        }
        if (!s.singleton())
            return false;

        return true;
    }
    
    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }

        if (var instanceof IntVar)
            return IntDomain.ANY;
        else
            return SetDomain.ANY;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise variant exists.");

    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer();
        result.append(id() + " : ChannelBoolSet(");
        result.append(Arrays.asList(b)).append(", ").append(s);
        result.append(", " + offset + ")");
        return result.toString();

    }
}
