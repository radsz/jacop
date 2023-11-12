/*
 * SeqPrecedeChain.java
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
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.lang.Integer;

/*
 * It defines Sequence Precedence Chain constraint for integers.  <p>
 * The constraint requires that i precedes i+1 in the array x for all
 * positive i (i > 0).
 * <p> The non-incremental algorithm is based on paper "Sequential
 * Precede Chain for value symmetry elimination " by Graeme Gange and
 * Peter J. Stuckey, Proc. International Conference on Principles and
 * Practice of Constraint Programming * (CP'2018).
 *
 * @author Krzysztof Kuchcinski
 * @version 4.9
 */
public class SeqPrecedeChain extends Constraint { 

    static final AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies lists of variables for the constraint.
     */
    final IntVar[] x;
    int n;

    int[] first;
    int[] last;

    /**
     * It constructs SeqPrecedeChain.
     *
     * @param x list of arguments x's.
     */
    public SeqPrecedeChain(IntVar[] x) {

        checkInputForNullness("x", x);

        this.numberId = idNumber.incrementAndGet();

        this.n = x.length;
        this.x = Arrays.copyOf(x, n);

        first = new int[n + 1];
        last = new int[n + 1];

        queueIndex = 1;

        setScope(Arrays.stream(x));
    }

    /**
     * It constructs SeqPrecedeChain.
     *
     * @param x list of arguments x's.
     */
    public SeqPrecedeChain(List<? extends IntVar> x) {
        this(x.toArray(new IntVar[x.size()]));
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public void consistency(Store store) {

        int up = 0;
        int low = 0;
        Arrays.fill(first, 0);
        Arrays.fill(last, n + 1);

        for (int i = 1; i < n + 1; i++) {
            IntVar xi = x[i - 1];

            if (xi.max() > up + 1)
                xi.domain.inMax(store.level, xi, up + 1);
            if (xi.max() == up + 1) {
                up++;
                first[up] = i;
            }
            if (low < xi.min()) {
                last[xi.min()] = i;
                low = xi.min();
            }
        }

        for (int i = n; i >= 1; i--) {
            IntVar xi = x[i - 1];

            last[i] = xi.min();
            if (first[low] == i) 
                xi.domain.inMin(store.level, xi, low);
            if (i <= last[low] && xi.domain.contains(low)) {
                last[i] = low;
                last[low] = i;
                low--;
                if (low < 0) break;
            }
        }
    }

    @Override public String toString() {

        StringBuilder resultString = new StringBuilder(id());

        resultString.append(" : SeqPrecedeChain([");
        int lx = x.length;
        for (int i = 0; i < lx; i++) {
            resultString.append(x[i]);
            if (i < lx - 1)
                resultString.append(", ");
        }
        resultString.append("])");

        return resultString.toString();
    }
}
