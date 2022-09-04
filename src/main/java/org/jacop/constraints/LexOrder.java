/*
 * LexOrder.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2010 Krzysztof Kuchcinski and Radoslaw Szymanek
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

import org.jacop.api.RemoveLevelLate;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.Stateful;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.TimeStamp;
import org.jacop.util.SimpleHashSet;
import java.util.Arrays;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;


/**
 * It constructs a LexOrder (lexicographical order) constraint.
 *
 * <p>The algorithm is based on paper
 *
 * <p>"Propagation algorithms for lexicographic ordering constraints" by
 * Alan M. Frisch, Brahim Hnich, Zeynep Kiziltan, Ian Miguel, and Toby Walsh ,
 * Artificial Intelligence 170 (2006) 803-834.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class LexOrder extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent, RemoveLevelLate {

    static AtomicInteger idNumber = new AtomicInteger(0);

    static final boolean debug = false;

    /**
     * Two vectors that have to be lexicographically ordered.
     */
    public IntVar[] x;
    public IntVar[] y;

    /**
     * Lex enforcing "{@literal <}" relationship (true).
     */
    public boolean lexLT;
    public boolean originalLexLT;

    /**
     * size of the longest vector.
     */
    int n;

    boolean satisfied;

    boolean firstConsistencyCheck = true;
    int firstConsistencyLevel;

    private Store store;

    private TimeStamp<Integer> alpha;
    private TimeStamp<Integer> beta;

    private int alphaValue;
    private int betaValue;

    SimpleHashSet<Integer> indexQueue = new SimpleHashSet<Integer>();
    Map<IntVar, int[]> varXToIndex = Var.createEmptyPositioning();
    Map<IntVar, int[]> varYToIndex = Var.createEmptyPositioning();

    /**
     * It creates a lexicographical order for vectors x and y,
     *
     * <p>vectors x and y does not need to be of the same size.
     * boolean lt defines if we require strict order, Lex_{{@literal <}} (lt = true) or Lex_{{@literal =<}} (lt = false).
     *
     * @param x first vector constrained by LexOrder constraint.
     * @param y second vector constrained by LexOrder constraint.
     */
    public LexOrder(IntVar[] x, IntVar[] y) {

        this(x, y, true);

        numberId = idNumber.incrementAndGet();

    }

    public LexOrder(IntVar[] x, IntVar[] y, boolean lt) {

        checkInputForNullness(new String[] {"x", "y"}, x, y);

        queueIndex = 2;
        numberId = idNumber.incrementAndGet();

        lexLT = lt;
        originalLexLT = lt;

        this.x = Arrays.copyOf(x, x.length);
        this.y = Arrays.copyOf(y, y.length);

        n = Math.min(x.length, y.length);

        // special cases; mostly on different sizes of vectors
        if (x.length > 0 && y.length == 0)
            lexLT = true;  // changing relation to "<" to generate non-satisfiablity; empty is not greater than any non-empty vector
        if (x.length == 0 && y.length > 0)
            lexLT = false;  // changing relation to "<=" to generate always satisfiablity; empty vector is always smaller
        if (x.length > 1 && y.length >= 1 && x.length > y.length)
            lexLT = true;  // changing relation to "<" to generate correct pruning; x is longer therefore y must be always lexicographically greater
        if (x.length >= 1 && y.length > 1 && x.length < y.length)
            lexLT = false;  // changing relation to "<=" to generate correct pruning;
                            //x is shorter therefore y must be always lexicographically greater or equal

        setScope(Stream.concat(Arrays.stream(x), Arrays.stream(y)));
    }

    @Override public void impose(Store store) {

        this.store = store;

        alpha = new TimeStamp<>(store, 0);
        beta = new TimeStamp<>(store, 0);

        for (int i = 0; i < n; i++) {
            int[] varPositions = varXToIndex.get(x[i]);
            if (varPositions == null) {
                int[] p = new int[1];
                p[0] = i;
                varXToIndex.put(x[i], p);
            } else {
                int[] newPos = new int[varPositions.length + 1];
                System.arraycopy(varPositions, 0, newPos, 0, varPositions.length);
                newPos[varPositions.length] = i;
                varXToIndex.put(x[i], varPositions);
            }
        }

        for (int i = 0; i < n; i++) {
            int[] varPositions = varYToIndex.get(y[i]);
            if (varPositions == null) {
                int[] p = new int[1];
                p[0] = i;
                varYToIndex.put(y[i], p);
            } else {
                int[] newPos = new int[varPositions.length + 1];
                System.arraycopy(varPositions, 0, newPos, 0, varPositions.length);
                newPos[varPositions.length] = i;
                varYToIndex.put(y[i], varPositions);
            }

        }

        store.registerRemoveLevelLateListener(this);

        super.impose(store);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public void consistency(Store store) {

        satisfied = false;

        if (firstConsistencyCheck) {

            establishGACInit();

            firstConsistencyCheck = false;
            firstConsistencyLevel = store.level;

        }

        alphaValue = alpha.value();
        betaValue = beta.value();

        do {

            store.propagationHasOccurred = false;

            SimpleHashSet<Integer> index = indexQueue;
            indexQueue = new SimpleHashSet<Integer>();

            while (!index.isEmpty()) {
                int i = index.removeFirst();

                if (!(i >= betaValue))
                    reestablishGAC(i);
            }

        } while (store.propagationHasOccurred);

        alpha.update(alphaValue);
        beta.update(betaValue);
    }

    @Override public boolean satisfied() {

        for (int i = 0; i < n; i++)
            if (x[i].max() < y[i].min())
                return true;
            else if (x[i].max() > y[i].min())
                return false;
            else if (eqSingletons(x[i], y[i]))
                if (lexLT) // <
                    return false;
                else // <=
                    if (i == n - 1)
                        return true;
                    else
                        continue;
            else
                return false;

        return false;
    }

    @Override public void queueVariable(int level, Var var) {

        int[] iValX = varXToIndex.get(var);
        int[] iValY = varYToIndex.get(var);

        if (iValX != null)
            for (int i : iValX)
                indexQueue.add(i);
        if (iValY != null)
            for (int i : iValY)
                indexQueue.add(i);

    }

    @Override public void removeLevel(int level) {
        if (level == firstConsistencyLevel)
            firstConsistencyCheck = true;
    }

    @Override public void removeLevelLate(int level) {

        indexQueue.clear();

    }


    @Override public String toString() {

        StringBuffer result = new StringBuffer();
        result.append(id());
        result.append(" : LexOrder(");

        result.append("[");

        for (int i = 0; i < x.length; i++) {
            result.append(x[i]);
            if (i < x.length - 1)
                result.append(", ");
        }

        result.append("], [");

        for (int i = 0; i < y.length; i++) {
            result.append(y[i]);
            if (i < y.length - 1)
                result.append(", ");
        }
        if (originalLexLT)
            result.append("], <");
        else
            result.append("], <=");

        result.append(");");

        return result.toString();

    }

    protected void establishGACInit() {

        satisfied = false;
        int a = 0;
        int b = 0;

        while (a < n && eqSingletons(x[a], y[a]))
            a++;

        if (debug)
            System.out.println("INIT entry: a = " + a);

        if (a == n) {
            if (!lexLT) {
                // alpha.update(a);
                // beta.update(n + 1);
                satisfied = true;
                removeConstraint();
                return; // satisfied already for le
            } else
                throw Store.failException; // fail for lt;
        } else {
            int i = a;
            b = -1;
            while (i != n && x[i].min() <= y[i].max()) {
                if (x[i].min() == y[i].max()) {
                    if (b == -1)
                        b = i;
                } else
                    b = -1;

                i++;
            }

            if (!lexLT) {
                if (i == n)
                    b = n + 1; //IntDomain.MaxInt;
                else if (b == -1)
                    b = i;
            } else if (b == -1)
                b = i;

            if (a >= b)
                throw Store.failException; // fail

            alpha.update(a);
            beta.update(b);
            alphaValue = a;
            betaValue = b;

            reestablishGAC(a);
        }

        if (debug)
            System.out.println("INIT exit: a = " + a + ", b = " + b);
    }

    void reestablishGAC(int i) {

        int a = alphaValue;
        int b = betaValue;

        if (debug) {
            System.out.println("reestablishGAC entry for " + i + ", alpha = " + a + ", beta = " + b);
            System.out.println(this);
        }

        if (a > b || satisfied) {
            removeConstraint();
            return;
        }

        if (i == a && (i + 1) == b)
            forceLT(i);

        if (i == a && (i + 1) < b) {
            forceLE(i);
            if (eqSingletons(x[i], y[i]))
                updateAlpha();
        }

        if (a < i && i < b)
            if ((i == (b - 1) && x[i].min() == y[i].max()) || x[i].min() > y[i].max())
                updateBeta(i - 1);

        if (debug) {
            System.out.println("reestablishGAC exit for " + i + ", alpha = " + a + ", beta = " + b);
            System.out.println(this);
        }
    }

    public void updateAlpha() {

        int a = alphaValue + 1;
        int b = betaValue;

        if (debug)
            System.out.println("updateAlpha entry: a = " + a + ", b = " + b);

        if (a == n)
            if (lexLT)
                throw Store.failException; // fail
            else {
                // alpha.update(a);
                satisfied = true;
                removeConstraint();
                return;
            }

        if (a == b)
            throw Store.failException; // fail

        if (!eqSingletons(x[a], y[a])) {
            alphaValue = a;
            reestablishGAC(a);
        } else {
            alphaValue = a;
            updateAlpha();
        }

        if (debug)
            System.out.println("updateAlfa exit: a = " + a + ", b = " + b);
    }

    public void updateBeta(int i) {

        int a = alphaValue;
        int b = i + 1;
        betaValue = b;

        if (debug)
            System.out.println("updateBeta entry: a = " + a + ", b = " + b);

        if (a == b)
            throw Store.failException; // fail

        if (x[i].min() < y[i].max()) {
            if (i == a)
                forceLT(i);
        } else // if (x[i].min() == y[i].max()) // ???
            updateBeta(i - 1);

        if (debug)
            System.out.println("updateBeta exit: a = " + a + ", b = " + b);
    }

    private boolean eqSingletons(IntVar x, IntVar y) {
        return x.singleton() && y.singleton() && x.value() == y.value();
    }

    private void forceLT(int i) {

        x[i].domain.inMax(store.level, x[i], y[i].max() - 1);
        y[i].domain.inMin(store.level, y[i], x[i].min() + 1);

    }

    private void forceLE(int i) {

        x[i].domain.inMax(store.level, x[i], y[i].max());
        y[i].domain.inMin(store.level, y[i], x[i].min());

    }

}
