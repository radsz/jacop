/*
 * Among.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2008 Polina Maakeva and Radoslaw Szymanek
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

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.*;

/**
 * Among constraint in its simplest form. It establishes the following
 * relation. The given number N of X`s take values from the supplied set
 * of values Kset. 
 *
 * This constraint implements a simple and polynomial algorithm to establish 
 * GAC as presented in different research papers. There are number of 
 * improvements (iterative execution, optimization of computational load upon 
 * backtracking) to improve the constraint further. 
 *
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 4.5
 */

public class Among extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

    private static final boolean debugAll = false;

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies the list of variables whose values are checked.
     */
    final public IntVar[] list;

    /**
     * It specifies a set of values which if assigned to a variable from a list makes variable counted.
     */
    final public IntervalDomain kSet;

    /**
     * It is a idNumber variable.
     */
    final public IntVar n;

    // number if x that belongs to K (Kset)
    // As search progress this time stamp can only increase
    // because if X was in between lbS and ubS than
    // it can have the between (x intersects S <> empty and x doesn't belong to
    // S) values being shrinked.
    private TimeStamp<Integer> lowerBorder;

    // number of x who may still intersect K (Kset)
    private TimeStamp<Integer> upperBorder;

    LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<IntVar>();

    private Map<IntVar, Integer> position;

    /**
     * It constructs an Among constraint.
     * @param list variables which are compared to Kset
     * @param kSet set of integer values against which we check if variables are equal to.
     * @param n number of possible variables equal to a value from Kset.
     */
    public Among(IntVar[] list, IntervalDomain kSet, IntVar n) {

        checkInputForNullness(new String[] {"list", "kSet", "n"}, new Object[][] { list, { kSet }, { n } });
        checkInputForDuplication("list", list);

        this.queueIndex = 1;
        numberId = idNumber.incrementAndGet();
        this.list = Arrays.copyOf(list, list.length);
        this.kSet = kSet.clone();
        this.n = n;

        setScope( Stream.concat(Arrays.stream(list), Stream.of(n)));

    }

    /**
     * It constructs an Among constraint.
     * @param list variables which are compared to Kset
     * @param kSet set of integer values against which we check if variables are equal to.
     * @param n number of possible variables equal to a value from Kset.
     */
    public Among(List<IntVar> list, IntervalDomain kSet, IntVar n) {
        this(list.toArray(new IntVar[list.size()]), kSet, n);
    }

    @Override public void removeLevel(int level) {
        variableQueue.clear();
    }

    @Override public void consistency(Store store) {
        // ----------------------------------------------------------
        if (debugAll) {
            System.out.println("LEVEL : " + store.level);
            System.out.println(this);
        }
        // ----------------------------------------------------------

        int currentLB = lowerBorder.value();
        // Refer to the algorithm where ubS = n - |{ x | dom(x) intersect S =
        // empty set } |
        int currentUB = upperBorder.value();

        // For the variable that signaled the change of domain
        // Count those that entered lbS, or ubS
        for (IntVar var : variableQueue) {

            int posVar = position.get(var);

            if (posVar < currentLB || posVar > currentUB)
                continue;

            if (kSet.contains(var.domain)) {

                assert posVar >= currentLB : "Variable " + var + " counted for lowerbound multiple times";

                if (posVar != currentLB) {
                    list[posVar] = list[currentLB];
                    list[currentLB] = var;
                    position.put(var, currentLB);
                    position.put(list[posVar], posVar);
                }
                currentLB++;

                // If variable entered lb then it would stay there
                // and we can detach the constrain from it
                var.removeConstraint(this);

            }
            if (!kSet.isIntersecting(var.domain)) {

                assert posVar <= currentUB : "Variable " + var + " counted for upperbound multiple times";

                if (posVar != currentUB) {
                    list[posVar] = list[currentUB - 1];
                    list[currentUB - 1] = var;
                    position.put(var, currentUB - 1);
                    position.put(list[posVar], posVar);
                }
                currentUB--;

                // If the variable entered not ub then it will stay there
                // and we can detach the constrain from it
                var.removeConstraint(this);

            }
        }

        variableQueue.clear();

        // ----------------------------------------------------------
        if (debugAll) {
            System.out.println("lbS = " + currentLB);
            System.out.println("ubS = " + currentUB);
            System.out.println(" domain of N " + n.domain + " is in [ " + currentLB + ", " + currentUB + " ]");
        }
        // ----------------------------------------------------------

        // Changed KK, 2015-10-17;
        // Not needed, in method will fail in such case
        // if (Math.max(n.min(), currentLB) > Math.min(n.max(), currentUB))
        // 	throw Store.failException;
        if (currentLB > currentUB)
            throw Store.failException;

        // n.domain.in(store.level, n, Math.max(n.min(), currentLB), Math.min(n.max(),
        // 		currentUB));

        // Changed KK, 2015-10-17;
        // Math.max is not needed since method in is doing
        // intersection between new domain and original domain
        n.domain.in(store.level, n, currentLB, currentUB);

        // Just in case LB or UB have changed.
        upperBorder.update(currentUB);
        lowerBorder.update(currentLB);

        if (currentLB == n.min() && n.domain.singleton()) {
            // If the number of X that belong to S is equal to N.value than we
            // have to subtract
            // the K set from the rest of x that do not belong to S
            for (int i = currentLB; i < currentUB; i++) {
                IntVar var = list[i];
                if (!kSet.contains(var.domain)) {
                    if (debugAll) {
                        System.out.println("lb >> The value before in of " + var.id + ": " + var.domain);
                        System.out.println("lb >> subtrack " + kSet);
                        System.out.println("lb >> equals " + var.domain.subtract(kSet));
                    }
                    var.domain.in(store.level, var, var.domain.subtract(kSet));
                    var.removeConstraint(this);
                    if (debugAll)
                        System.out.println("lb >> The value after in of " + var.id + ": " + var.domain);
                }
            }

            // since the constraint is satisfied UB is equal to LB.
            upperBorder.update(currentLB);

            // The constrain became satisfied
            if (debugAll)
                System.out.println("Simple Among is satisfied");
        }

        if (currentUB == n.min() && n.domain.singleton()) {
            // If the number intersecting X is equal to desired number N than we
            // have
            // to intersect the domains of X with K set.
            for (int i = currentLB; i < currentUB; i++) {
                IntVar var = list[i];
                var.domain.in(store.level, var, kSet);
                var.removeConstraint(this);
            }

            // since the constraint is satisfied LB is equal to UB.
            lowerBorder.update(currentUB);

            // The constrain became satisfied
            if (debugAll)
                System.out.println("Simple Among is satisfied");
        }

        if (debugAll)
            System.out.println(this);
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public void impose(Store store) {

        super.impose(store);

        this.lowerBorder = new TimeStamp<>(store, 0);
        this.upperBorder = new TimeStamp<>(store, list.length);

        position = Var.positionMapping(list, false, this.getClass());


    }

    @Override public void queueVariable(int level, Var var) {
        if (debugAll)
            System.out.println("Var " + var + ((IntVar) var).recentDomainPruning());

        if (var != n)
            variableQueue.add((IntVar) var);
    }

    @Override public boolean satisfied() {
        return (Objects.equals(lowerBorder.value(), upperBorder.value()) && n.min() == lowerBorder.value() && n.singleton());
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(": Among([");

        for (IntVar var : this.list)
            result.append(var).append(" ");

        result.append("], ").append(this.kSet).append(", ");
        result.append(n).append(")\n");

        return result.toString();
    }

}
