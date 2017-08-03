/**
 * LinearInt.java
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
import org.jacop.core.Store;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * LinearInt constraint implements the weighted summation over several
 * variables .
 * <p>
 * sum(i in 1..N)(ai*xi) = b
 * <p>
 * It provides the weighted sum from all variables on the list.
 * The weights are integers.
 * <p>
 * This implementaiton is based on
 * "Bounds Consistency Techniques for Long Linear Constraints"
 * by Warwick Harvey and Joachim Schimpf
 *
 * @author Krzysztof Kuchcinski
 * @version 4.4
 */

public class LinearInt extends PrimitiveConstraint {

    Store store;

    static AtomicInteger idNumber = new AtomicInteger(0);

    boolean reified = true;

    /**
     * Defines relations
     */
    final static byte eq = 0, le = 1, lt = 2, ne = 3, gt = 4, ge = 5;

    /**
     * Defines negated relations
     */
    final static byte[] negRel = {ne, //eq=0,
        gt, //le=1,
        ge, //lt=2,
        eq, //ne=3,
        le, //gt=4,
        lt  //ge=5;
    };

    /**
     * It specifies what relations is used by this constraint
     */

    public byte relationType;

    /**
     * It specifies a list of variables being summed.
     */
    IntVar x[];

    /**
     * It specifies a list of weights associated with the variables being summed.
     */
    int a[];

    /**
     * It specifies variable for the overall sum.
     */
    int b;

    /**
     * It specifies the index of the last positive coefficient.
     */
    int pos;

    /**
     * It specifies the number of variables/coefficients.
     */
    int l;

    /**
     * It specifies "variability" of each variable
     */
    int[] I;

    /**
     * It specifies sum of lower bounds (min values) and sum of upper bounds (max values)
     */
    int sumMin, sumMax;

    protected LinearInt() {
    }

    /**
     * @param store   current store
     * @param list    variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param rel     the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum     the sum of weighted variables.
     */
    public LinearInt(Store store, IntVar[] list, int[] weights, String rel, int sum) {
        checkInputForNullness("list", list);
        checkInputForNullness("weights", weights);
        commonInitialization(store, list, weights, rel, sum);
        numberId = idNumber.incrementAndGet();
    }

    /**
     * It constructs the constraint LinearInt.
     *
     * @param store   current store
     * @param list    list which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param rel     the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum     the sum of weighted list.
     */
    public LinearInt(Store store, ArrayList<? extends IntVar> list, ArrayList<Integer> weights, String rel, int sum) {
        checkInputForNullness(new String[] {"list", "weights"}, new Object[] {list, weights});
        commonInitialization(store, list.toArray(new IntVar[list.size()]), weights.stream().mapToInt(i -> i).toArray(), rel, sum);
        numberId = idNumber.incrementAndGet();
    }

    /**
     * @param store   current store
     * @param list    variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param rel     the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum     the sum of weighted variables.
     */
    public LinearInt(Store store, IntVar[] list, int[] weights, String rel, IntVar sum) {
        checkInputForNullness("list", list);
        checkInputForNullness("weights", weights);
        commonInitialization(store, Stream.concat(Arrays.stream(list), Stream.of(sum)).toArray(IntVar[]::new),
            IntStream.concat(Arrays.stream(weights), IntStream.of(-1)).toArray(), rel, 0);
        numberId = idNumber.incrementAndGet();
    }

    protected void commonInitialization(Store store, IntVar[] list, int[] weights, String rel, int sum) {

        this.relationType = relation(rel);

        assert (list.length == weights.length) : "\nLength of two vectors different in Propagations";

        this.store = store;
        this.b = sum;

        LinkedHashMap<IntVar, Integer> parameters = new LinkedHashMap<IntVar, Integer>();

        for (int i = 0; i < list.length; i++) {

            assert (list[i] != null) : i + "-th element of list in Propagations constraint is null";
            if (weights[i] != 0) {
                if (list[i].singleton())
                    this.b -= list[i].value() * weights[i];
                else if (parameters.get(list[i]) != null) {
                    // variable ordered in the scope of the Propagations constraint.
                    Integer coeff = parameters.get(list[i]);
                    Integer sumOfCoeff = coeff + weights[i];
                    parameters.put(list[i], sumOfCoeff);
                } else
                    parameters.put(list[i], weights[i]);

            }
        }
        int size = 0;
        for (Integer e : parameters.values())
            if (e != 0)
                size++;

        this.x = new IntVar[size];
        this.a = new int[size];

        int i = 0;
        Set<Map.Entry<IntVar, Integer>> entries = parameters.entrySet();

        for (Map.Entry<IntVar, Integer> e : entries) {
            IntVar var = e.getKey();
            int coeff = e.getValue();
            if (coeff > 0) {
                this.x[i] = var;
                this.a[i] = coeff;
                i++;
            }
        }
        pos = i;
        for (Map.Entry<IntVar, Integer> e : entries) {
            IntVar var = e.getKey();
            int coeff = e.getValue();
            if (coeff < 0) {
                this.x[i] = var;
                this.a[i] = coeff;
                i++;
            }
        }

        this.l = x.length;
        this.I = new int[l];

        checkForOverflow();

        if (l <= 3)
            queueIndex = 0;
        else
            queueIndex = 1;

        setScope(list);

    }

    @Override public void consistency(Store store) {

        propagate(relationType);
    }

    @Override public void notConsistency(Store store) {
        propagate(negRel[relationType]);
    }

    public void propagate(int rel) {

        computeInit();

        do {

            store.propagationHasOccurred = false;

            switch (rel) {
                case eq:

                    pruneLtEq(b);
                    pruneGtEq(b);

                    // if (!reified)
                    //     if (sumMax <= b && sumMin >= b)
                    // 	removeConstraint();

                    break;

                case le:
                    pruneLtEq(b);

                    if (!reified)
                        if (sumMax <= b)
                            removeConstraint();
                    break;

                case lt:
                    pruneLtEq(b - 1);

                    if (!reified)
                        if (sumMax < b)
                            removeConstraint();
                    break;
                case ne:
                    pruneNeq();

                    if (!reified)
                        // if (sumMin == sumMax && (sumMin > b || sumMax < b))
                        if (sumMin > b || sumMax < b)
                            removeConstraint();
                    break;
                case gt:

                    pruneGtEq(b + 1);

                    if (!reified)
                        if (sumMin > b)
                            removeConstraint();
                    break;
                case ge:

                    pruneGtEq(b);

                    if (!reified)
                        if (sumMin >= b)
                            removeConstraint();

                    break;
                default:
                    throw new RuntimeException("Internal error in " + getClass().getName());
            }

        } while (store.propagationHasOccurred);
    }


    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    // TODO, Why do we keep having those weird checks.
    // Include method missing?
    @Override public void impose(Store store) {

        if (x == null || x.length == 0)
            return;

        reified = false;

        super.impose(store);

    }

    void computeInit() {
        int f = 0, e = 0;
        int min, max;
        int i = 0;
        // positive weights
        for (; i < pos; i++) {
            IntDomain xd = x[i].dom();
            min = xd.min() * a[i];
            max = xd.max() * a[i];
            f += min;
            e += max;
            I[i] = (max - min);
        }
        // negative weights
        for (; i < l; i++) {
            IntDomain xd = x[i].dom();
            min = xd.max() * a[i];
            max = xd.min() * a[i];
            f += min;
            e += max;
            I[i] = (max - min);
        }
        sumMin = f;
        sumMax = e;
    }


    void pruneLtEq(int b) {

        if (sumMin > b)
            throw store.failException;

        int min, max;
        int i = 0;
        // positive weights
        for (; i < pos; i++) {
            if (I[i] > b - sumMin) {
                min = x[i].min() * a[i];
                max = min + I[i];
                if (pruneMax(x[i], divRoundDown(b - sumMin + min, a[i]))) {
                    int newMax = x[i].max() * a[i];
                    sumMax -= max - newMax;
                    I[i] = newMax - min;
                }
            }
        }
        // negative weights
        for (; i < l; i++) {
            if (I[i] > b - sumMin) {
                min = x[i].max() * a[i];
                max = min + I[i];
                if (pruneMin(x[i], divRoundUp(-(b - sumMin + min), -a[i]))) {
                    int newMax = x[i].min() * a[i];
                    sumMax -= max - newMax;
                    I[i] = newMax - min;
                }
            }
        }
    }

    void pruneGtEq(int b) {

        if (sumMax < b)
            throw store.failException;

        int min, max;
        int i = 0;
        // positive weights
        for (; i < pos; i++) {
            if (I[i] > -(b - sumMax)) {
                max = x[i].max() * a[i];
                min = max - I[i];
                if (pruneMin(x[i], divRoundUp(b - sumMax + max, a[i]))) {
                    int nmin = x[i].min() * a[i];
                    sumMin += nmin - min;
                    I[i] = max - nmin;
                }
            }
        }
        // negative weights
        for (; i < l; i++) {
            if (I[i] > -(b - sumMax)) {
                max = x[i].min() * a[i];
                min = max - I[i];
                if (pruneMax(x[i], divRoundDown(-(b - sumMax + max), -a[i]))) {
                    int newMin = x[i].max() * a[i];
                    sumMin += newMin - min;
                    I[i] = max - newMin;
                }
            }
        }
    }

    void pruneNeq() {

        if (sumMin == sumMax && b == sumMin)
            throw store.failException;

        int min, max;
        int i = 0;
        // positive weights
        for (; i < pos; i++) {
            min = x[i].min() * a[i];
            max = min + I[i];

            if (pruneNe(x[i], b - sumMax + max, b - sumMin + min, a[i])) {
                int newMin = x[i].min() * a[i];
                int newMax = x[i].max() * a[i];
                sumMin += newMin - min;
                sumMax += newMax - max;
                I[i] = newMax - newMin;
            }
        }
        // negative weights
        for (; i < l; i++) {
            min = x[i].max() * a[i];
            max = min + I[i];

            if (pruneNe(x[i], b - sumMin + min, b - sumMax + max, a[i])) {
                int newMin = x[i].max() * a[i];
                int newMax = x[i].min() * a[i];
                sumMin += newMin - min;
                sumMax += newMax - max;
                I[i] = newMax - newMin;
            }
        }
    }

    private boolean pruneMin(IntVar x, int min) {
        if (min > x.min()) {
            x.domain.inMin(store.level, x, min);
            return true;
        } else
            return false;
    }

    private boolean pruneMax(IntVar x, int max) {
        if (max < x.max()) {
            x.domain.inMax(store.level, x, max);
            return true;
        } else
            return false;
    }

    private boolean pruneNe(IntVar x, int min, int max, int a) {

        if (min == max && min % a == 0) {

            int d = min / a;

            boolean boundsChanged = false;

            if (d == x.min() || d == x.max())
                boundsChanged = true;

            x.domain.inComplement(store.level, x, d);

            return boundsChanged;
        }
        return false;
    }

    public boolean satisfiedEq() {

        int sMin = 0, sMax = 0;
        int i = 0;
        for (; i < pos; i++) {
            sMin += x[i].min() * a[i];
            sMax += x[i].max() * a[i];
        }
        for (; i < l; i++) {
            sMin += x[i].max() * a[i];
            sMax += x[i].min() * a[i];
        }

        return sMin == sMax && sMin == b;
    }

    public boolean satisfiedNeq() {

        int sMax = 0, sMin = 0;
        int i = 0;
        for (; i < pos; i++) {
            sMin += x[i].min() * a[i];
            sMax += x[i].max() * a[i];
        }
        for (; i < l; i++) {
            sMin += x[i].max() * a[i];
            sMax += x[i].min() * a[i];
        }

        return sMin > b || sMax < b;
    }

    public boolean satisfiedLtEq(int b) {

        int sMax = 0;
        int i = 0;
        for (; i < pos; i++) {
            sMax += x[i].max() * a[i];
        }
        for (; i < l; i++) {
            sMax += x[i].min() * a[i];
        }

        return sMax <= b;
    }

    public boolean satisfiedGtEq(int b) {

        int sMin = 0;
        int i = 0;
        for (; i < pos; i++) {
            sMin += x[i].min() * a[i];
        }
        for (; i < l; i++) {
            sMin += x[i].max() * a[i];
        }

        return sMin >= b;
    }


    @Override public boolean satisfied() {
        return entailed(relationType);
    }

    @Override public boolean notSatisfied() {
        return entailed(negRel[relationType]);
    }

    private boolean entailed(int rel) {

        switch (rel) {
            case eq:
                return satisfiedEq();
            case le:
                return satisfiedLtEq(b);
            case lt:
                return satisfiedLtEq(b - 1);
            case ne:
                return satisfiedNeq();
            case gt:
                return satisfiedGtEq(b + 1);
            case ge:
                return satisfiedGtEq(b);
        }

        return false;
    }

    private int divRoundDown(int a, int b) {
        if (a >= 0)
            return a / b;
        else // a < 0
            return (a - b + 1) / b;
    }

    private int divRoundUp(int a, int b) {
        if (a >= 0)
            return (a + b - 1) / b;
        else // a < 0
            return a / b;
    }

    // private int divFloor(int s, int a) {
    // 	return (int)( Math.floor ( (float)s / a ) );
    // }

    // private int divCeil(int s, int a) {
    // 	return (int)(  Math.ceil( (float)s / a ) );
    // }

    public byte relation(String r) {
        if (r.equals("=="))
            return eq;
        else if (r.equals("="))
            return eq;
        else if (r.equals("<"))
            return lt;
        else if (r.equals("<="))
            return le;
        else if (r.equals("=<"))
            return le;
        else if (r.equals("!="))
            return ne;
        else if (r.equals(">"))
            return gt;
        else if (r.equals(">="))
            return ge;
        else if (r.equals("=>"))
            return ge;
        else {
            System.err.println("Wrong relation symbol in LinearInt constraint " + r + "; assumed ==");
            return eq;
        }
    }

    public String rel2String() {
        switch (relationType) {
            case eq:
                return "==";
            case lt:
                return "<";
            case le:
                return "<=";
            case ne:
                return "!=";
            case gt:
                return ">";
            case ge:
                return ">=";
        }

        return "?";
    }

    void checkForOverflow() {

        int sMin = 0, sMax = 0;
        int i = 0;
        for (; i < pos; i++) {
            int n1 = Math.multiplyExact(x[i].min(), a[i]);
            int n2 = Math.multiplyExact(x[i].max(), a[i]);

            sMin = Math.addExact(sMin, n1);
            sMax = Math.addExact(sMax, n2);
        }
        for (; i < l; i++) {
            int n1 = Math.multiplyExact(x[i].max(), a[i]);
            int n2 = Math.multiplyExact(x[i].min(), a[i]);

            sMin = Math.addExact(sMin, n1);
            sMax = Math.addExact(sMax, n2);
        }
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : LinearInt( [ ");

        for (int i = 0; i < x.length; i++) {
            result.append(x[i]);
            if (i < x.length - 1)
                result.append(", ");
        }
        result.append("], [");

        for (int i = 0; i < a.length; i++) {
            result.append(a[i]);
            if (i < a.length - 1)
                result.append(", ");
        }

        result.append("], ").append(rel2String()).append(", ").append(b).append(" )");

        return result.toString();

    }

}
