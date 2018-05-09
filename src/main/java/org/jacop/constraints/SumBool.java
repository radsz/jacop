/*
 * SumBool.java
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

import java.util.Arrays;
import java.util.List;
import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

import org.jacop.core.IntVar;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * SumBool constraint implements the summation over several
 * 0/1 variables. 
 *
 * sum(i in 1..N)(xi) = sum
 *
 * It provides the sum from all variables on the list.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class SumBool extends PrimitiveConstraint {

    Store store;

    final static AtomicInteger idNumber = new AtomicInteger(0);

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
     * @param store current store
     * @param list variables which are being multiplied by weights.
     * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum variable containing the sum of weighted variables.
     * @deprecated SumBool constraint does not use Store parameter any longer.
     */
    @Deprecated
    public SumBool(Store store, IntVar[] list, String rel, IntVar sum) {

        checkInputForNullness(new String[]{"list", "rel", "sum"}, new Object[][]{list, {rel}, {sum}});
        checkInput(list, l -> l.min() >= 0 && l.max() <= 1, "domain must lie within 0..1 domain" );

        numberId = idNumber.incrementAndGet();
        this.relationType = relation(rel);
        this.store = store;
        this.sum = sum;
        x = filterAndOverflow(list); //Arrays.copyOf(list, list.length);
        this.l = x.length;

        if (l <= 2)
            queueIndex = 0;
        else
            queueIndex = 1;

        setScope( Stream.concat( Stream.of(sum), Arrays.stream(list) ) );
    }

    /**
     * It constructs the constraint SumBool. 
     * @param store current store
     * @param variables variables which are being multiplied by weights.
     * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum variable containing the sum of weighted variables.
     * @deprecated SumBool constraint does not use Store parameter any longer.
     */
    @Deprecated
    public SumBool(Store store, List<? extends IntVar> variables, String rel, IntVar sum) {
        this(store, variables.toArray(new IntVar[variables.size()]), rel, sum);
    }

    /**
     * @param list variables which are being multiplied by weights.
     * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum variable containing the sum of weighted variables.
     */
    public SumBool(IntVar[] list, String rel, IntVar sum) {
	this(sum.getStore(), list, rel, sum);
    }

    /**
     * It constructs the constraint SumBool. 
     * @param variables variables which are being multiplied by weights.
     * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum variable containing the sum of weighted variables.
     */
    public SumBool(List<? extends IntVar> variables, String rel, IntVar sum) {
        this(variables.toArray(new IntVar[variables.size()]), rel, sum);
    }

    @Override public void consistency(Store store) {
        prune(relationType);
    }

    @Override public void notConsistency(Store store) {
        prune(negRel[relationType]);
    }

    private void prune(byte rel) {

        int min = 0;
        int max = 0;

        for (int i = 0; i < l; i++) {
            IntDomain xd = x[i].dom();
            min += xd.min();
            max += xd.max();
        }

        switch (rel) {
            case eq:

                sum.domain.in(store.level, sum, min, max);

                if (sum.singleton() && min != max) {
                    int sumValue = sum.value();
                    if (sumValue == min)
                        for (int i = 0; i < l; i++)
                            if (!x[i].singleton())
                                x[i].domain.in(store.level, x[i], 0, 0);

                    if (sumValue == max)
                        for (int i = 0; i < l; i++)
                            if (!x[i].singleton())
                                x[i].domain.in(store.level, x[i], 1, 1);
                }
                break;
            case le:

                sum.domain.inMin(store.level, sum, min);

                if (!reified)
                    if (max <= sum.min())
                        removeConstraint();

                if (sum.singleton() && min != max) {
                    int sumValue = sum.value();
                    if (sumValue == min)
                        for (int i = 0; i < l; i++)
                            if (!x[i].singleton())
                                x[i].domain.in(store.level, x[i], 0, 0);
                }
                break;
            case lt:

                sum.domain.inMin(store.level, sum, min + 1);

                if (!reified)
                    if (max < sum.min())
                        removeConstraint();

                if (sum.singleton() && min != max) {
                    int sumValue = sum.value();
                    if (sumValue - 1 == min)
                        for (int i = 0; i < l; i++)
                            if (!x[i].singleton())
                                x[i].domain.in(store.level, x[i], 0, 0);

                }
                break;
            case ne:

                if (min == max)
                    sum.domain.inComplement(store.level, sum, min);

                int sumMin = sum.min() - max, sumMax = sum.max() - min;
                if (sumMax - sumMin == 1)
                    for (int i = 0; i < l; i++)
                        if (!x[i].singleton())
                            x[i].domain.inComplement(store.level, x[i], sumMin + x[i].max());
                break;
            case gt:

                sum.domain.inMax(store.level, sum, max - 1);

                if (!reified)
                    if (min > sum.max())
                        removeConstraint();

                if (sum.singleton() && min != max) {
                    int sumValue = sum.value();

                    if (sumValue + 1 == max)
                        for (int i = 0; i < l; i++)
                            if (!x[i].singleton())
                                x[i].domain.in(store.level, x[i], 1, 1);
                }
                break;
            case ge:

                sum.domain.inMax(store.level, sum, max);

                if (!reified)
                    if (min >= sum.max())
                        removeConstraint();

                if (sum.singleton() && min != max) {
                    int sumValue = sum.value();

                    if (sumValue == max)
                        for (int i = 0; i < l; i++)
                            if (!x[i].singleton())
                                x[i].domain.in(store.level, x[i], 1, 1);
                }
                break;
        }
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }
    
    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
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

    @Override public boolean satisfied() {

        return entailed(relationType);

    }

    @Override public boolean notSatisfied() {

        return entailed(negRel[relationType]);

    }

    private boolean entailed(byte rel) {

        int min = 0, max = 0;

        for (int i = 0; i < l; i++) {
            IntDomain xd = x[i].dom();
            min += xd.min();
            max += xd.max();
        }

        switch (rel) {
            case eq:
                return sum.singleton(min) && min == max;
            case lt:
                return max < sum.min();
            case le:
                return max <= sum.min();
            case ne:
                return sum.min() > max || sum.max() < min; //sum.singleton() && min == max && sum.min() != min;
            case gt:
                return min > sum.max();
            case ge:
                return min >= sum.max();
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

    IntVar[] filterAndOverflow(IntVar[] x) {

	List<IntVar> ls = new ArrayList<>();
	
        int sMin = 0, sMax = 0;
        for (int i = 0; i < x.length; i++) {
            int n1 = x[i].min();
            int n2 = x[i].max();

            sMin = Math.addExact(sMin, n1);
            sMax = Math.addExact(sMax, n2);

	    if (x[i].max() != 0)
		ls.add(x[i]);
        }

	return ls.toArray(new IntVar[ls.size()]);	    
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : SumBool( [ ");

        for (int i = 0; i < l; i++) {
            result.append(x[i]);
            if (i < l - 1)
                result.append(", ");
        }
        result.append("], ");

        result.append(rel2String()).append(", ").append(sum).append(" )");

        return result.toString();

    }

}
