/*
 * ValuePrecede.java
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

import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.*;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

/*
 * It defines Value Precedence constraint for integers.
 * <p>
 * Value precedence of s over t in an integer sequence x = [x0,..., xn−1]
 * means if there exists j such that xj = t, then there must
 * exist i {@literal <} j such that xi = s.
 * <p>
 * The algorithm is based on paper
 * "Global Constraints for Integer and Set Value Precedence" by
 * Y. C. Law, J. H. Lee
 * Principles and Practice of Constraint Programming (CP'2004).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */
public class ValuePrecede extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

    static final AtomicInteger idNumber = new AtomicInteger(0);

    Store store;

    /**
     * It specifies lists of variables for the constraint.
     */
    public final IntVar[] x;
    private int n;

    /**
     * It specifies values s and t for the constraint.
     */
    protected final int s;
    protected final int t;

    /*
     * Defines variables alpha, beta, gamma for the algorithm
     */
    private TimeStamp<Integer> alpha;
    private TimeStamp<Integer> beta;
    private TimeStamp<Integer> gamma;

    private int  alphaValue;
    private int  betaValue;
    private int  gammaValue;

    private boolean firstConsistencyCheck = true;

    private LinkedHashSet<IntVar> varQueue = new LinkedHashSet<>();

    private final Map<IntVar, Integer> varMap;


    /**
     * It constructs ValuePrecede.
     *
     * @param s value occuring first
     * @param t value occuring next
     * @param x list of arguments x's.
     */
    public ValuePrecede(int s, int t, IntVar[] x) {

        checkInputForNullness("x", x);
        checkInputForDuplication("x", x);

        this.numberId = idNumber.incrementAndGet();

        this.s = s;
        this.t = t;
        this.n = x.length;
        this.x = Arrays.copyOf(x, n);

        queueIndex = 1;

        varMap = Var.positionMapping(x, false, this.getClass());

        setScope(Arrays.stream(x));
    }

    /**
     * It constructs ValuePrecede.
     *
     * @param s value occuring first
     * @param t value occuring next
     * @param x list of arguments x's.
     */
    public ValuePrecede(int s, int t, List<IntVar> x) {
        this(s, t, x.toArray(new IntVar[x.size()]));
    }


    // registers the constraint in the constraint store and
    // initialize stateful variables
    @Override public void impose(Store store) {

        this.store = store;

        super.impose(store);

        alpha = new TimeStamp<>(store, 0);
        beta = new TimeStamp<>(store, 0);
        gamma = new TimeStamp<>(store, 0);

        alphaValue = 0;
        betaValue = 0;
        gammaValue = 0;

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    /*
     *
     */
    @Override public void consistency(Store store) {

        if (firstConsistencyCheck) {
            initialize();
            firstConsistencyCheck = false;
        }

        alphaValue = alpha.value();
        betaValue = beta.value();
        gammaValue = gamma.value();
        
        do {

            store.propagationHasOccurred = false;

            LinkedHashSet<IntVar> fdvs = varQueue;
            varQueue = new LinkedHashSet<IntVar>();

            for (IntVar v : fdvs) {
                int i = varMap.get(v);
                propagate(i);
            }

        } while (store.propagationHasOccurred);

        alpha.update(alphaValue);
        beta.update(betaValue);
        gamma.update(gammaValue);
    }

    private void initialize() {
        int a = alphaValue;
        while (a < n && !x[a].domain.contains(s)) {
            x[a].domain.inComplement(store.level, x[a], t);
            a++;
        }
        alphaValue = a;
        betaValue = a;
        gammaValue = a;

        int g = a;
        if (a < n) {
            x[a].domain.inComplement(store.level, x[a], t);
            do {
                g++;
            } while (g < n && !x[g].singleton(t));
            gammaValue = g;
            updateBeta();
        }

        alpha.update(alphaValue);
        beta.update(betaValue);
        gamma.update(gammaValue);
    }

    private void propagate(int i) {
        int b = betaValue;
        if (b <= gammaValue) {
            int a = alphaValue;
            if (i == a && !x[i].domain.contains(s)) {
                a++;
                while (a < b) {
                    x[a].domain.inComplement(store.level, x[a], t);
                    a++;
                }
                while (a < n && !x[a].domain.contains(s)) {
                    x[a].domain.inComplement(store.level, x[a], t);
                    a++;
                }
                if (a < n) {
                    x[a].domain.inComplement(store.level, x[a], t);
                }
                alphaValue = a;
                betaValue = a;
                if (a < n) {
                    updateBeta();
                }
            } else if (i == b && !x[i].domain.contains(s)) {
                updateBeta();
            }
        }
        checkGamma(i);
    }

    private void updateBeta() {
        int b = betaValue;
        do {
            b++;
        } while (b < n && !x[b].domain.contains(s));

        if (b > gammaValue) {
            int a = alphaValue;
            x[a].domain.inValue(store.level, x[a], s);
            removeConstraint();
        }
        betaValue = b;
    }

    private void checkGamma(int i) {
        int g = gammaValue;
        if (betaValue < g && i < g && x[i].singleton(t)) {
            gammaValue = i;
            if (betaValue > i) {
                int a = alphaValue;
                x[a].domain.inValue(store.level, x[a], s);
                removeConstraint();
            }
        }
    }


    @Override public boolean satisfied() {

        int firstS = -1;
        int firstT = -1;
        for (int i = 0; i < x.length; i++) {
            if (x[i].singleton()) {
                if (firstS == -1 && x[i].singleton(s))
                    firstS = i;
                if (firstT == -1 && x[i].singleton(t))
                    firstT = i;
            } else
                return false;
        }

        return (firstT != -1 && firstS < firstT) || (firstS == -1 && firstT == -1);
    }

    @Override public void queueVariable(int level, Var var) {
        varQueue.add((IntVar) var);
    }

    @Override public void removeLevel(int level) {
        varQueue.clear();
    }

    @Override public String toString() {

        StringBuilder resultString = new StringBuilder(id());

        resultString.append(" : ValuePrecede(" + s + ", " + t + ", [");
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
