/*
 * SumInt.java
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
import org.jacop.core.Var;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * SumInt constraint implements the summation over several variables.
 * <p>
 * sum(i in 1..N)(xi) = sum
 * <p>
 * It provides the sum from all variables on the list.
 * <p>
 * This implementaiton is based on
 * "Bounds Consistency Techniques for Long Linear Constraints"
 * by Warwick Harvey and Joachim Schimpf
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class SumInt extends PrimitiveConstraint {

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
     * It specifies variable for the overall sum.
     */
    IntVar sum;

    /**
     * It specifies the number of variables.
     */
    int l;

    /**
     * It specifies "variability" of each variable
     */
    long[] I;

    /**
     * It specifies sum of lower bounds (min values) and sum of upper bounds (max values)
     */
    long sumXmin, sumXmax;

    /**
     * @param store current store
     * @param list  variables which are being multiplied by weights.
     * @param rel   the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum   variable containing the sum of weighted variables.
     * @deprecated SumInt constraint does not use Store parameter any longer.
     */
    @Deprecated
    public SumInt(Store store, IntVar[] list, String rel, IntVar sum) {

        checkInputForNullness(new String[] {"list", "rel", "sum"}, new Object[][] {list, {rel}, {sum}});

        this.relationType = relation(rel);
        this.store = store;
        this.sum = sum;

        x = Arrays.copyOf(list, list.length);
        numberId = idNumber.incrementAndGet();

        this.l = x.length;
        this.I = new long[l];

        // checkForOverflow();

        if (l <= 2)
            queueIndex = 0;
        else
            queueIndex = 1;

        setScope(Stream.concat(Arrays.stream(list), Stream.of(sum)));

    }

    /**
     * It constructs the constraint SumInt.
     *
     * @param store     current store
     * @param variables variables which are being multiplied by weights.
     * @param rel       the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum       variable containing the sum of weighted variables.
     * @deprecated SumInt constraint does not use Store parameter any longer.
     */
    @Deprecated
    public SumInt(Store store, List<? extends IntVar> variables, String rel, IntVar sum) {
        this(store, variables.toArray(new IntVar[variables.size()]), rel, sum);
    }

    /**
     * @param list  variables which are being multiplied by weights.
     * @param rel   the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum   variable containing the sum of weighted variables.
     */
    public SumInt(IntVar[] list, String rel, IntVar sum) {
	this(sum.getStore(), list, rel, sum);
    }

    /**
     * It constructs the constraint SumInt.
     *
     * @param variables variables which are being multiplied by weights.
     * @param rel       the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum       variable containing the sum of weighted variables.
     *
     */
    public SumInt(List<? extends IntVar> variables, String rel, IntVar sum) {
        this(variables.toArray(new IntVar[variables.size()]), rel, sum);
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

                    pruneLtEq(0L);
                    pruneGtEq(0L);

                    // if (sumXmax == sumXmin && sum.singleton() && sum.value() == sumXmin)
                    //     removeConstraint();

                    break;

                case le:
                    pruneLtEq(0L);

                    if (!reified)
                        if (sumXmax <= sum.min())
                            removeConstraint();
                    break;

                case lt:
                    pruneLtEq(1L);

                    if (!reified)
                        if (sumXmax < sum.min())
                            removeConstraint();
                    break;
                case ne:
                    pruneNeq();

                    if (!reified)
                        // if (sumXmin == sumXmax && sum.singleton() && sumXmin != sum.value())
                        if (sumXmin > sum.max() || sumXmax < sum.min())
                            removeConstraint();
                    break;
                case gt:

                    pruneGtEq(1L);

                    if (!reified)
                        if (sumXmin > sum.max())
                            removeConstraint();
                    break;
                case ge:

                    pruneGtEq(0L);

                    if (!reified)
                        if (sumXmin >= sum.max())
                            removeConstraint();

                    break;
                default:
                    throw new RuntimeException("Internal error in " + getClass().getName());
            }

        } while (store.propagationHasOccurred);
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public void impose(Store store) {

        if (x == null)
            return;

        reified = false;

        super.impose(store);

    }

    private void computeInit() {
        long f = 0, e = 0;
        long min, max;

        for (int i = 0; i < l; i++) {
            IntDomain xd = x[i].dom();
            min = (long)xd.min();
            max = (long)xd.max();
            f += min;
            e += max;
            I[i] = (max - min);
        }

        sumXmin = f;
        sumXmax = e;
    }

    private void pruneLtEq(long b) {

        sum.domain.inMin(store.level, sum, long2int(sumXmin + b));

        long min, max;
        long sMax = (long)sum.max();

        for (int i = 0; i < l; i++) {
            if (I[i] > (sMax - sumXmin - b)) {
                min = (long)x[i].min();
                max = min + I[i];
                if (pruneMax(x[i], sMax - sumXmin + min - b)) {
                    long newMax = (long)x[i].max();
                    sumXmax -= max - newMax;
                    I[i] = newMax - min;
                }
            }
        }
    }

    private void pruneGtEq(long b) {

        sum.domain.inMax(store.level, sum, long2int(sumXmax - b));

        long min, max;
        long sMin = (long)sum.min();

        for (int i = 0; i < l; i++) {
            if (I[i] > -(sMin - sumXmax + b)) {
                max = (long)x[i].max();
                min = max - I[i];
                if (pruneMin(x[i], (sMin - sumXmax + max + b))) {
                    long newMin = (long)x[i].min();
                    sumXmin += newMin - min;
                    I[i] = max - newMin;
                }
            }
        }
    }

    private void pruneNeq() {

        if (sumXmin == sumXmax)
            sum.domain.inComplement(store.level, sum, long2int(sumXmin));
        store.propagationHasOccurred = false;

        long min, max;

        for (int i = 0; i < l; i++) {
            min = (long)x[i].min();
            max = min + I[i];

            if (pruneNe(x[i], (long)sum.min() - sumXmax + max, sum.max() - sumXmin + min)) {
                long newMin = (long)x[i].min();
                long newMax = (long)x[i].max();
                sumXmin += newMin - min;
                sumXmax += newMax - max;
                I[i] = newMax - newMin;
            }
        }
    }

    private boolean pruneMin(IntVar x, long min) {
        if (min > (long)x.min()) {
            x.domain.inMin(store.level, x, long2int(min));
            return true;
        } else
            return false;
    }

    private boolean pruneMax(IntVar x, long max) {
        if (max < (long)x.max()) {
            x.domain.inMax(store.level, x, long2int(max));
            return true;
        } else
            return false;
    }

    private boolean pruneNe(IntVar x, long min, long max) {

        if (min == max) {
            boolean boundsChanged = false;
            if (min == (long)x.min() || max == (long)x.max())
                boundsChanged = true;

            x.domain.inComplement(store.level, x, long2int(min));

            return boundsChanged;
        }

        return false;
    }

    public boolean satisfiedEq() {

        long sMin = 0, sMax = 0;

        for (int i = 0; i < l; i++) {
            sMin += (long)x[i].min();
            sMax += (long)x[i].max();
        }

        return sMax <= (long)sum.min() && sMin >= (long)sum.max(); //sMin == sMax && sMin == sum.min() && sMin == sum.max();
    }

    public boolean satisfiedNeq() {

        long sMax = 0, sMin = 0;

        for (int i = 0; i < l; i++) {
            sMin += (long)x[i].min();
            sMax += (long)x[i].max();
        }

        return sMin > (long)sum.max() || sMax < (long)sum.min();
    }

    public boolean satisfiedLtEq(int b) {

        long sMax = 0;

        for (int i = 0; i < l; i++) {
            sMax += (long)x[i].max();
        }

        return sMax <= (long)sum.min() - b;
    }

    public boolean satisfiedGtEq(int b) {

        long sMin = 0;

        for (int i = 0; i < l; i++) {
            sMin += (long)x[i].min();
        }

        return sMin >= (long)sum.max() + b;
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
                return satisfiedLtEq(0);
            case lt:
                return satisfiedLtEq(1);
            case ne:
                return satisfiedNeq();
            case gt:
                return satisfiedGtEq(1);
            case ge:
                return satisfiedGtEq(0);
        }

        return false;
    }

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
            System.err.println("Wrong relation symbol in SumInt constraint " + r + "; assumed ==");
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

    // void checkForOverflow() {

    //     long sMin = -(long)sum.max(), sMax = -(long)sum.min();
    //     for (int i = 0; i < x.length; i++) {
    //         sMin = Math.addExact(sMin, (long)x[i].min());
    //         sMax = Math.addExact(sMax, (long)x[i].max());
    //     }
    // }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : SumInt( [ ");

        for (int i = 0; i < l; i++) {
            result.append(x[i]);
            if (i < l - 1)
                result.append(", ");
        }
        result.append("], ");

        result.append(rel2String()).append(", ").append(sum).append(" )");

        return result.toString();

    }


    @Override public Constraint getGuideConstraint() {

        IntVar proposedVariable = (IntVar) getGuideVariable();
        if (proposedVariable != null)
            return new XeqC(proposedVariable, guideValue);
        else
            return null;
    }

    @Override public int getGuideValue() {
        return guideValue;
    }

    int guideValue = 0;


    @Override public Var getGuideVariable() {

        int regret = 1;
        Var proposedVariable = null;

        for (IntVar v : x) {

            IntDomain listDom = v.dom();

            if (v.singleton())
                continue;

            int currentRegret = listDom.nextValue(listDom.min()) - listDom.min();

            if (currentRegret > regret) {
                regret = currentRegret;
                proposedVariable = v;
                guideValue = listDom.min();
            }

            currentRegret = listDom.max() - listDom.previousValue(listDom.max());

            if (currentRegret > regret) {
                regret = currentRegret;
                proposedVariable = v;
                guideValue = listDom.max();
            }

        }

        return proposedVariable;

    }


    @Override public void supplyGuideFeedback(boolean feedback) {
    }

}
