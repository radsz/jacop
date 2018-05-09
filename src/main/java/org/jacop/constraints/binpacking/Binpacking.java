/*
 * Binpacking.java
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


package org.jacop.constraints.binpacking;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.*;
import org.jacop.util.SimpleHashSet;
import java.util.stream.Stream;

/**
 * Binpacking constraint implements bin packing problem. It ensures that
 * items are packed into bins while respecting cpacity constraints of each bin.
 * <p>
 * This implementation is based on paper "A Constraint for Bin Packing" by
 * Paul Shaw, CP 2004.
 *
 * This constraint is not idempotent (does not compute fix-point) and,
 * in case when another computation for fix-point is needed, it adds
 * itself to the constraint queue.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Binpacking extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

    final private static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It keeps together a list of variables which define bin for item i and
     * their weigts.
     */
    final public BinItem[] item;

    /**
     * It specifies a list of variables which define bin load.
     */
    final public IntVar[] load;

    private boolean firstConsistencyCheck = true;

    private int minBinNumber = 0;

    private int sizeAllItems = 0;

    private int alphaP = 0, betaP = 0;

    final private SimpleHashSet<IntVar> itemQueue = new SimpleHashSet<>();
    final private SimpleHashSet<IntVar> binQueue = new SimpleHashSet<>();

    private final Map<IntVar, Integer> itemMap;
    private final Map<IntVar, Integer> binMap;

    /**
     * It constructs the binpacking constraint for the supplied variable.
     *
     * @param bin  which are constrained to define bin for item i.
     * @param load which are constrained to define load for bin i.
     * @param w    which define size ofitem i.
     */
    public Binpacking(IntVar[] bin, IntVar[] load, int[] w) {

        checkInputForNullness(new String[]{"bin", "load", "w"}, new Object[][]{bin, load, {w}});
        checkInputForDuplication("load", load);
        checkInput(w, t -> t >= 0, "weight for item is not >=0");

        if (bin.length != w.length)
            throw new IllegalArgumentException("Constraint BinPacking has arguments bin and w that are of different sizes");

        LinkedHashMap<IntVar, Integer> itemPar = new LinkedHashMap<>();
        for (int i = 0; i < bin.length; i++) {

            if (w[i] != 0)
                if (itemPar.get(bin[i]) != null) {
                    Integer s = itemPar.get(bin[i]);
                    Integer ns = s + w[i];
                    itemPar.put(bin[i], ns);
                } else
                    itemPar.put(bin[i], w[i]);
        }

        this.numberId = idNumber.incrementAndGet();
        this.item = new BinItem[itemPar.size()];
        this.queueIndex = 2;

        minBinNumber = bin[0].min();
        Set<Map.Entry<IntVar, Integer>> entries = itemPar.entrySet();
        int j = 0;
        for (Map.Entry<IntVar, Integer> e : entries) {
            IntVar b = e.getKey();
            int ws = e.getValue();
            item[j] = new BinItem(b, ws);

            sizeAllItems += ws;

            if (minBinNumber > b.min())
                minBinNumber = b.min();
            j++;
        }

        this.load = Arrays.copyOf(load, load.length);

        binMap = Var.positionMapping(load, false, this.getClass());

        Comparator<BinItem> weightComparator = (o1, o2) -> (o2.weight - o1.weight);
        Arrays.sort(item, weightComparator);

        itemMap = Var.positionMapping(Arrays.stream(item).map( i -> i.bin ).toArray(IntVar[]::new),
            false, this.getClass());

        setScope(Stream.concat(Arrays.stream(item).map(i -> i.bin), Arrays.stream(load)));
    }

    /**
     * It constructs the binpacking constraint for the supplied variable.
     *
     * @param bin  which are constrained to define bin for item i.
     * @param load which are constrained to define load for bin i.
     * @param w    which define size ofitem i.
     */

    public Binpacking(List<? extends IntVar> bin, List<? extends IntVar> load, int[] w) {
        this(bin.toArray(new IntVar[bin.size()]), load.toArray(new IntVar[load.size()]), w);
    }

    /**
     * It constructs the binpacking constraint for the supplied variable.
     *
     * @param bin    which are constrained to define bin for item i.
     * @param load   which are constrained to define load for bin i.
     * @param w      which define size ofitem i.
     * @param minBin minimal index of a bin; ovewrite the value provided by minimal index of variable bin
     */
    public Binpacking(IntVar[] bin, IntVar[] load, int[] w, int minBin) {
        this(bin, load, w);
        minBinNumber = minBin;
    }

    /**
     * It constructs the binpacking constraint for the supplied variable.
     *
     * @param bin    which are constrained to define bin for item i.
     * @param load   which are constrained to define load for bin i.
     * @param w      which define size ofitem i.
     * @param minBin minimal index of a bin; ovewrite the value provided by minimal index of variable bin
     */
    public Binpacking(List<? extends IntVar> bin, List<? extends IntVar> load, int[] w, int minBin) {

        this(bin.toArray(new IntVar[bin.size()]), load.toArray(new IntVar[load.size()]), w);
        minBinNumber = minBin;
    }

    @Override public void consistency(Store store) {

        // Rule "Pack All" -- chcecked only first time
        if (firstConsistencyCheck) {

            Arrays.stream(item)
                .map( i -> i.bin )
                .forEach( i -> i.domain.in(store.level, i, minBinNumber, load.length - 1 + minBinNumber));

            firstConsistencyCheck = false;
        }

	store.propagationHasOccurred = false;

	// we check bins that changed recently only
	// it means:
	//      - load[i] variables have changed,
	//      - item[i] variables have changed (we check both current domain and pruned values)
	IntervalDomain d = new IntervalDomain();
	while (binQueue.size() != 0) {
	    IntVar var = binQueue.removeFirst();
	    int i = binMap.get(var) + minBinNumber;
	    d.addDom(new IntervalDomain(i, i));
	}
	while (itemQueue.size() != 0) {
	    IntVar var = itemQueue.removeFirst();
	    IntDomain pd = var.dom().previousDomain;
	    if (pd != null)
		d.addDom(pd);
	    else
		d.addDom(var.dom());
	}

	BinItem[] candidates;
	// for (int i = 0; i < load.length; i++) {  // replaced with needed bins to check
	for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
	    int i = e.nextElement() - minBinNumber;

	    // check if bin no. is in the limits; might not be there since it is FDV specified in by a user
	    if (i >= 0 && i < load.length) {

		candidates = new BinItem[item.length];
		int candidatesLength = 0;

		int required = 0;
		int possible = 0;

		for (BinItem itemEl : item) {
		    //  		    System.out.println (itemEl.bin + " prunned = "+itemEl.bin.dom().recentDomainPruning(store.level));

		    if (itemEl.bin.dom().contains(i + minBinNumber)) {
			possible += itemEl.weight;
			if (itemEl.bin.singleton())
			    required += itemEl.weight;
			else // not singleton
			    candidates[candidatesLength++] = itemEl;
		    }
		}

		// 		    System.out.println ("load " + i + "  " +required +".."+possible);

		// Rule "Load Maintenance"
		load[i].domain.in(store.level, load[i], required, possible);

		for (int l = 0; l < candidatesLength; l++) {
		    BinItem bi = candidates[l];
		    if (required + bi.weight > load[i].max())
			bi.bin.domain.inComplement(store.level, bi.bin, i + minBinNumber);
		    else if (possible - bi.weight < load[i].min())
			bi.bin.domain.in(store.level, bi.bin, i + minBinNumber, i + minBinNumber);
		}

		// Rule 3.2 "Search Pruning"
		int[] Cj = new int[candidatesLength];
		for (int l = 0; l < candidatesLength; l++)
		    Cj[l] = candidates[l].weight;

		if (no_sum(Cj, load[i].min() - required, load[i].max() - required))
		    throw Store.failException;

		// Rule 3.3 "Tighteing Bounds on Bin Load"
		if (no_sum(Cj, load[i].min() - required, load[i].min() - required))
		    load[i].domain.inMin(store.level, load[i], required + betaP);

		if (no_sum(Cj, load[i].max() - required, load[i].max() - required))
		    load[i].domain.inMax(store.level, load[i], required + alphaP);

		// Rule 3.4 "Elimination and Commitment of Items"
		for (int j = 0; j < candidatesLength; j++) {
		    int[] CjMinusI = new int[candidatesLength - 1];
		    System.arraycopy(Cj, 0, CjMinusI, 0, j);
		    System.arraycopy(Cj, j + 1, CjMinusI, j, (Cj.length - j - 1));

		    if (no_sum(CjMinusI, load[i].min() - required - Cj[j], load[i].max() - required - Cj[j]))
			candidates[j].bin.domain.inComplement(store.level, candidates[j].bin, i + minBinNumber);
		    if (no_sum(CjMinusI, load[i].min() - required, load[i].max() - required))
			candidates[j].bin.domain.in(store.level, candidates[j].bin, i + minBinNumber, i + minBinNumber);
		}
	    }
	}

	int allCapacityMin = 0, allCapacityMax = 0;
	for (IntVar aLoad : load) {
	    allCapacityMin += aLoad.min();
	    allCapacityMax += aLoad.max();
	}

	// Rule "Load and Size Coherence"
	int s1 = sizeAllItems - allCapacityMax;
	int s2 = sizeAllItems - allCapacityMin;
	for (IntVar aLoad : load)
	    aLoad.domain.in(store.level, aLoad,
			    s1 + aLoad.max(),
			    s2 + aLoad.min());

	// since the constraint is not idempotent (does not compute
	// fix-point) we need to add it to the constraint queue for
	// re-evaluation, if there was a changed in any of variables
	if (store.propagationHasOccurred)
	    store.addChanged(this);

        // Lower bound pruning
        int[] unpacked = new int[item.length];
        int unpackedLength = 0;
        int[] a = new int[load.length];
        Arrays.fill(a, 0);

        for (BinItem itemI : item) {
            if (itemI.bin.singleton()) {
                int p = itemI.bin.value() - minBinNumber;
                a[p] += itemI.weight;
            } else
                unpacked[unpackedLength++] = itemI.weight;
        }

        int maxCapacity = 0;
        for (IntVar maxC : load)
            if (maxCapacity < maxC.max())
                maxCapacity = maxC.max();

        for (int i = 0; i < load.length; i++)
            if (a[i] != 0)   // consider only already loaded bins to add additional "load"
                a[i] += maxCapacity - load[i].max();

        Arrays.sort(a);  // sort array a in ascending order

        int[] z = merge(unpacked, unpackedLength, a);

        // if number of possible bins is lower than lower bound then fail
        if (getNumberBins(item) < lbBins(z, maxCapacity))
            throw Store.failException;
    }

    private int getNumberBins(BinItem[] item) {
        int min = IntDomain.MaxInt, max = 0;
        for (BinItem anItem : item) {
            IntVar bin = anItem.bin;
            int bmin = bin.min(), bmax = bin.max();
            max = (max > bmax) ? max : bmax;
            min = (min < bmin) ? min : bmin;
        }
        return max - min + 1;
    }


    private int[] merge(int[] u, int uLength, int[] a) {
        int[] tmp = new int[a.length + uLength];

        int i = 0, j = a.length - 1, k = 0;

        while (i < uLength && j >= 0) {
            if (a[j] > u[i] || i >= uLength)
                if (a[j] != 0)
                    tmp[k++] = a[j--];
                else
                    j--;
            else
                tmp[k++] = u[i++];
        }
        while (i < uLength)
            tmp[k++] = u[i++];
        while (j >= 0)
            if (a[j] != 0)
                tmp[k++] = a[j--];
            else
                j--;

        return tmp;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public boolean satisfied() {

        if (!grounded())
            return false;

        return false;

    }

    @Override public void queueVariable(int level, Var var) {
        if (itemMap.containsKey(var))
            itemQueue.add((IntVar) var);
        else 
            binQueue.add((IntVar) var);
    }

    @Override public void removeLevel(int level) {
        itemQueue.clear();
        binQueue.clear();
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : binpacking([");

        for (int i = 0; i < item.length; i++) {
            result.append(item[i].bin);
            if (i < item.length - 1)
                result.append(", ");
        }
        result.append("], [");
        for (int i = 0; i < load.length; i++) {
            result.append(load[i]);
            if (i < load.length - 1)
                result.append(", ");
        }
        result.append("], [");
        for (int i = 0; i < item.length; i++) {
            result.append(item[i].weight);
            if (i < item.length - 1)
                result.append(", ");
        }
        result.append("])");

        return result.toString();

    }

    private boolean no_sum(int[] X, int alpha, int beta) {

        if (alpha <= 0 || beta >= sum(X))
            return false;

        int sum_a = 0, sum_b, sum_c = 0, k = 0, kPrime = 0, N = X.length - 1; // |X|

        while (sum_c + X[N - kPrime] < alpha) {
            sum_c += X[N - kPrime];
            kPrime++; // += 1;
        }
        // 	System.out.println("sum_c = " + sum_c + " k' = " + kPrime);

        sum_b = X[N - kPrime];
        while (sum_a < alpha && sum_b <= beta) {
            // 	    System.out.println(sum_a +" < " +alpha + "  "+sum_b + " <= " + beta);
            sum_a += X[k++];
            if (sum_a < alpha) {
                kPrime--; // -= 1;
                sum_b += X[N - kPrime];
                sum_c -= X[N - kPrime];
                while (sum_a + sum_c >= alpha) {
                    kPrime -= 1;
                    sum_c -= X[N - kPrime];
                    sum_b += X[N - kPrime] - X[N - kPrime - k - 1];
                }
            }
        }
        // 	System.out.println("k = "+k+" k' = "+kPrime);
        // 	System.out.println("sum_a = "+sum_a+" sum_b = "+sum_b+" sum_c = "+sum_c) ;

        alphaP = sum_a + sum_c;
        betaP = sum_b;

        return sum_a < alpha;
    }

    private int sum(int[] x) {
        int summa = 0;
        for (int v : x)
            summa += v;
        return summa;
    }

    private int lbBins(int[] X, int C) {

        int sum = sum(X);
        int lb = sum / C + ((sum % C != 0) ? 1 : 0);

        int[] N = new int[3];

        for (int K = 0; K <= C / 2; K++) {
	    Arrays.fill(N, 0);

            int i = 0;
            while (i < X.length && X[i] > C - K) {
                N[0] += 1;
                i += 1;
            }

            int freeSpaceN1 = 0;
            while (i < X.length && X[i] > C / 2) {
                N[1] += 1;
                freeSpaceN1 += C - X[i];
                i += 1;
            }

            int sizeInN2 = 0;
            while (i < X.length && X[i] >= K) {
                N[2] += 1;
                sizeInN2 += X[i];
                i += 1;
            }

            int toPack = sizeInN2 - freeSpaceN1;
            int noBinsN2 = 0;
            if (toPack > 0)
                noBinsN2 = toPack / C + ((toPack % C > 0) ? 1 : 0);

            int currentLb = N[0] + N[1] + noBinsN2;

            if (currentLb > lb)
                lb = currentLb;

        }
        return lb;
    }

}
