/*
 * ChannelImply.java
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

import org.jacop.core.*;
import org.jacop.api.SatisfiedPresent;
import java.util.Arrays;
import java.util.Map;
import java.util.HashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * ChannelImply constraints "B {@literal =>} constraint".
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class ChannelImply extends Constraint implements SatisfiedPresent {

    static final AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * Variables that is checked for a value.
     */
    public final IntVar x;
    
    /**
     * length of vector bs.
     */
    final int n;
    
    /**
     * It specifies variables b and related values for variable x.
     */
    final Item[] item;

    private TimeStamp<Integer> position;

    Map<Integer,IntVar> valueMap = new HashMap<>();

    /**
     * It creates ChannelImply constraint.
     *
     * @param x variable to be checked.
     * @param bs array representing the status of equality x = i.
     * @param value array of values that are checked against x.
     */
    public ChannelImply(IntVar x, IntVar[] bs, int[] value) {

        if (value.length != bs.length)
            throw new IllegalArgumentException("ChannelImply: Status array size ("
                                               + bs.length
                                               + "), has not equal size as number of values "
                                               + value.length);

        checkInputForNullness(new String[] {"x", "bs"}, new Object[][] {{x}, bs});
        for (IntVar b : bs)
            if (b.min() > 1 || b.max() < 0)
                throw new IllegalArgumentException("ChannelImply: Variable b in reified constraint must have domain at most 0..1");

        numberId = idNumber.incrementAndGet();
        this.x = x;
        this.n = bs.length;

        item = new Item[n];
        for (int i = 0; i < n; i++)
            item[i] = new Item(bs[i], value[i]);

        for (int i = 0; i < value.length; i++)
            valueMap.put(value[i], bs[i]);

        setScope(Stream.concat(Stream.of(x), Arrays.stream(bs)));
        this.queueIndex = 0;
    }

    /**
     * It creates ChannelImply constraint.
     *
     * @param x variable to be checked.
     * @param bs array representing the status of equality x = i.
     * @param value set of values that are checked against x.
     */
    public ChannelImply(IntVar x, IntVar[] bs, IntDomain value) {
        this(x, bs, toArray(value));
    }

    public ChannelImply(IntVar x, IntVar[] bs) {

        this(x, bs, toArray(x.domain));
    }

    public ChannelImply(IntVar x, Map<Integer, ? extends IntVar> bs) {

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.n = bs.size();

        item = new Item[n];
        IntVar[] bbs = new IntVar[n];
        int i = 0;
        for (Map.Entry<Integer, ? extends IntVar> e : bs.entrySet()) {
            int val = e.getKey();
            IntVar b = e.getValue();
            item[i] = new Item(b, val);

            valueMap.put(val, b);
            bbs[i] = b;
            i++;
        }

        setScope(Stream.concat(Stream.of(x), Arrays.stream(bbs)));
        this.queueIndex = 0;
    }

    static int[] toArray(IntDomain d) {

        int[] vs = new int[d.getSize()];
        int i = 0;
        for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
            int v = e.nextElement();
            vs[i++] = v;
        }
        return vs;
    }
    
    @Override public void consistency(final Store store) {

        int start = position.value();
        boolean startChanged = false;

        for (int i = start; i < n; i++) {

            if (item[i].b.max() == 0) {
                swap(start, i);
                start++;
                startChanged = true;
                continue;
            } else if (item[i].b.min() == 1)
                x.domain.inValue(store.level, x, item[i].value);

            if (! x.domain.contains(item[i].value)) {
                item[i].b.domain.inValue(store.level, item[i].b, 0);
                swap(start, i);
                start++;
                startChanged = true;
            }
        }

        if (startChanged)
            position.update(start);

        if (start == n) {
            if (! x.singleton())
                removeConstraint();
            return;
        }

        if (x.singleton()) {
            IntVar b = valueMap.get(x.value());

            for (int i = start; i < n; i++)
                if (item[i].b != b)
                    item[i].b.domain.inValue(store.level, item[i].b, 0);
                
        }

    }

    private void swap(int i, int j) {
        if (i != j) {
            Item tmp = item[i];
            item[i] = item[j];
            item[j] = tmp;
        }
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    public boolean satisfied() {

        int one = Integer.MIN_VALUE;
        if (x.singleton()) {
            for (int i = 0; i < n; i++) {
                if (item[i].b.singleton()) {
                    if (item[i].b.value() == 1)
                        if (one == -1)
                            one = i;
                        else
                            return false;
                    else
                        return false;
                } else
                    return false;
            }
        } else
            return false;

        return (one == Integer.MIN_VALUE) ? false : x.value() == item[one].value;
    }

    @Override public void impose(Store store) {

        super.impose(store);

        position = new TimeStamp<>(store, 0);
    }

    @Override public String toString() {

        return id() + " : ChannelImply(" + x + ", " + Arrays.asList(item) + " )";
    }

    static class Item {

        int value;
        IntVar b;

        public Item(IntVar b, int v) {
            this.b = b;
            this.value = v;
        }

        public String toString() {

            return "[" + b + ", " + value + "]";
        }
    }
}
