/**
 *  Binpacking.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


package org.jacop.constraints.binpacking;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;

import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.SimpleHashSet;

/**
 * Binpacking constraint implements bin packing problem. It ensures that
 * items are packed into bins while respecting cpacity constraints of each bin.
 *
 * This implementation is based on paper "A Constraint for Bin Packing" by
 * Paul Shaw, CP 2004.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Binpacking extends Constraint {

	static int idNumber = 1;

	/**
	 * It keeps together a list of variables which define bin for item i and
	 * their weigts.
	 */
	public BinItem[] item;

	/**
	 * It specifies a list of variables which define bin load.
	 */
	public IntVar[] load;

	boolean firstConsistencyCheck = true;

	int minBinNumber = 0;

	int sizeAllItems = 0;

	int alphaP=0, betaP=0;

	SimpleHashSet<IntVar> itemQueue = new SimpleHashSet<IntVar>();
	SimpleHashSet<IntVar> binQueue = new SimpleHashSet<IntVar>();

	HashMap<IntVar, Integer> itemMap = new HashMap<IntVar, Integer>();
	HashMap<IntVar, Integer> binMap = new HashMap<IntVar, Integer>();

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"bin"};

	/**
	 * It constructs the binpacking constraint for the supplied variable.
	 * @param bin which are constrained to define bin for item i.
	 * @param load which are constrained to define load for bin i.
	 * @param w which define size ofitem i.
	 */
	public Binpacking(IntVar[] bin, IntVar[] load, int[] w) {

		assert (bin != null) : "Variables bin is null";
		assert (load != null) : "Variables load is null";
		assert (w != null) : "Integer array w is null";
		assert (bin.length == w.length) : "Lists in bin packing constraints have different sizes";

		this.numberId = idNumber++;
		this.item = new BinItem[bin.length];
		this.numberArgs = (short) bin.length + load.length;
		this.queueIndex = 1;

		minBinNumber = bin[0].min();
		for (int i = 0; i < bin.length; i++) {
			assert (bin[i] != null) : i + "-th element in bin list is null";
			item[i] = new BinItem(bin[i], w[i]);

			sizeAllItems += w[i];

			if (minBinNumber > item[i].bin.min()) minBinNumber = item[i].bin.min();
		}

		this.load = new IntVar[load.length];
		for (int i = 0; i < load.length; i++) {
			assert (load[i] != null) : i + "-th element in load list is null";
			this.load[i] = load[i];

			binMap.put(this.load[i], i);

		}

		Arrays.sort(item, new WeightComparator<BinItem>());
		for (int i = 0; i < item.length; i++) 
			itemMap.put(item[i].bin, i);
	}

	/**
	 * It constructs the binpacking constraint for the supplied variable.
	 * @param bin which are constrained to define bin for item i.
	 * @param load which are constrained to define load for bin i.
	 * @param w which define size ofitem i.
	 */

	public Binpacking(ArrayList<? extends IntVar> bin,
			ArrayList<? extends IntVar> load,
			int[] w) {

		this(bin.toArray(new IntVar[bin.size()]), 
				load.toArray(new IntVar[load.size()]), 
				w);
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> Variables = new ArrayList<Var>(item.length+load.length);

		for (int i = 0; i < item.length; i++) {
			Variables.add(item[i].bin);
		}

		Variables.addAll(Arrays.asList(load));

		return Variables;
	}

	@Override
	public void consistency(Store store) {

		// Rule "Pack All" -- chcecked only first time
		if (firstConsistencyCheck) {
			for (int i = 0; i < item.length; i++) 
				item[i].bin.domain.in(store.level, item[i].bin, minBinNumber, load.length - 1 + minBinNumber);

			firstConsistencyCheck = false;
		}

		do {
			store.propagationHasOccurred = false;

			// we check bins that changed recently only
			// it means: 
			//      - load[i] variables have changed,
			//      - item variables have changed (we check both current domain and pruned values) 
			IntervalDomain d = new IntervalDomain();
			while (binQueue.size() != 0 ) {
				IntVar var = binQueue.removeFirst();
				int i = binMap.get(var) + minBinNumber;
				d.addDom(new IntervalDomain(i,i));
			}
			while (itemQueue.size() != 0 ) {
				IntVar var = itemQueue.removeFirst();
				d.addDom(var.dom());
				d.addDom(var.dom().recentDomainPruning(store.level));
			}

			ArrayList<BinItem> candidates;
			//   	    for (int i = 0; i < load.length; i++) {  // replaced with needed bins to check
			for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements();) {
				int i = e.nextElement() - minBinNumber;

				if ( i >= 0 && i < load.length) { // check if bin no. is in the limits; might not be there since it is FDV specified in by a user

					candidates = new ArrayList<BinItem>();
					int required = 0;
					int possible = 0;

					for (BinItem itemEl : item) {
						//  		    System.out.println (itemEl.bin + " prunned = "+itemEl.bin.dom().recentDomainPruning(store.level));

						if (itemEl.bin.dom().contains(i + minBinNumber)) {
							possible += itemEl.weight;
							if (itemEl.bin.singleton())
								required += itemEl.weight;
							else // not singleton
								candidates.add(itemEl);
						}
					}

					// 		    System.out.println ("load " + i + "  " +required +".."+possible);

					// Rule "Load Maintenance"
					load[i].domain.in(store.level, load[i], required, possible);

					for (BinItem bi : candidates) 
						if ( required + bi.weight > load[i].max()) 
							bi.bin.domain.inComplement(store.level, bi.bin, i + minBinNumber);
							else if (possible - bi.weight < load[i].min() ) 
								bi.bin.domain.in(store.level, bi.bin, i + minBinNumber, i + minBinNumber);

							// Rule 3.2 "Search Pruning"
							int[] Cj = new int[candidates.size()];
							int index=0;
							for (BinItem bi : candidates) 
								Cj[index++] = bi.weight; 

									if (no_sum(Cj, load[i].min() - required, load[i].max() - required)) 
										throw Store.failException;

									// Rule 3.3 "Tighteing Bounds on Bin Load"
									if (no_sum(Cj, load[i].min() - required, load[i].min() - required))
										load[i].domain.inMin(store.level, load[i], required + betaP);

									if (no_sum(Cj, load[i].max() - required, load[i].max() - required))
										load[i].domain.inMax(store.level, load[i], required + alphaP);

									// Rule 3.4 "Elimination and Commitment of Items"
									for (int j = 0; j < candidates.size(); j++) {
										int[] CjMinusI = new int[candidates.size() - 1];
										System.arraycopy(Cj, 0, CjMinusI, 0, j);
										System.arraycopy(Cj, j+1, CjMinusI, j, (Cj.length - j - 1));

										// 			for (int k = 0; k < candidates.size(); k++) {
										// 			    if ( k != j)
										// 				CjMinusI[l++] = candidates.get(k).weight;
										// 			}

										if (no_sum(CjMinusI, load[i].min() - required - Cj[j], load[i].max() - required - Cj[j])) 
											candidates.get(j).bin.domain.inComplement(store.level, candidates.get(j).bin, i+minBinNumber);
										if (no_sum(CjMinusI, load[i].min() - required, load[i].max() - required)) 
											candidates.get(j).bin.domain.in(store.level, candidates.get(j).bin, i+minBinNumber, i+minBinNumber);
									}
				}
			}

			int allCapacityMin = 0, allCapacityMax = 0;
			for (int i = 0; i < load.length; i++) {
				allCapacityMin += load[i].min();
				allCapacityMax += load[i].max();
			}

			// Rule "Load and Size Coherence"
			for (int i = 0; i < load.length; i++)
				load[i].domain.in(store.level, load[i], sizeAllItems - (allCapacityMax - load[i].max()), 
						sizeAllItems - (allCapacityMin - load[i].min()));


		} while (store.propagationHasOccurred);


		// Lower bound pruning
		ArrayList<Integer> unpacked = new ArrayList<Integer>();
		int[] a = new int[load.length];
		Arrays.fill(a, 0);

		for (BinItem itemI : item) {
			if (itemI.bin.singleton()) {
				int p = itemI.bin.value() - minBinNumber;
				a[p] += itemI.weight;
			}
			else
				unpacked.add(itemI.weight);
		}

		int maxCapacity = 0;
		for (IntVar maxC : load)
			if (maxCapacity < maxC.max())
				maxCapacity = maxC.max();

				for (int i = 0; i < load.length; i++)
					if (a[i] != 0)   // consider only already loaded bins to add additional "load"
						a[i] += maxCapacity - load[i].max();

				Arrays.sort(a);  // sort array a in ascending order

				int[] z = merge(unpacked, a);

				// if number of possible bins is lower than lower bound then fail
				if (getNumberBins(item) < lbBins(z, maxCapacity))
					throw Store.failException;
	}

	int getNumberBins(BinItem[] item) {
		int min = IntDomain.MaxInt, max = 0;
		for (int i = 0; i < item.length; i++) {
			max = (max > item[i].bin.max()) ? max : item[i].bin.max();
			min = (min < item[i].bin.min()) ? min : item[i].bin.min();
		}
		return max - min + 1;
	}


	int[] merge(ArrayList<Integer> u, int[] a) {
		ArrayList<Integer> tmp = new ArrayList<Integer>(a.length+u.size());

		int i=0, j=a.length-1;

		while (i < u.size() && j >= 0) {
			if (a[j] > u.get(i) || i >= u.size())
				if (a[j] != 0) tmp.add(a[j--]);
				else j--;
			else
				tmp.add(u.get(i++));
		}
		while (i < u.size())
			tmp.add(u.get(i++));
		while (j >= 0)
			if (a[j] != 0) tmp.add(a[j--]);
			else j--;

		//   	System.out.println (tmp.size() + "  *** "+ tmp);
		int[] arr = new int[tmp.size()];
		for (int k = 0; k < tmp.size(); k++)
			arr[k] = tmp.get(k);

		return arr;
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return IntDomain.ANY;
	}

	@Override
	public boolean satisfied() {
		boolean allBinsSingleton = true;

		int i=0;
		while (i < item.length && allBinsSingleton)
			allBinsSingleton = item[i++].bin.singleton();

		return allBinsSingleton;

	}

	@Override
	public void impose(Store store) {

		for (BinItem el : item) {
			el.bin.putModelConstraint(this, getConsistencyPruningEvent(el.bin));
			queueVariable(store.level, el.bin);
		}
		for (IntVar v : load) {
			v.putModelConstraint(this, getConsistencyPruningEvent(v));
		}

		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void queueVariable(int level, Var V) {
		if (itemMap.get(V) != null)
			itemQueue.add((IntVar)V);
		else
			binQueue.add((IntVar)V);	    
	}

	@Override
	public void removeLevel(int level) {
		itemQueue.clear();
		binQueue.clear();
	}

	@Override
	public void removeConstraint() {
		for (BinItem v : item)
			v.bin.removeConstraint(this);
				for (Var v : load)
					v.removeConstraint(this);
	}


	@Override
	public String toString() {

		StringBuffer result = new StringBuffer( id() );

		result.append(" : binpacking([");

		for (int i = 0; i < item.length; i++) {
			result.append(item[i].bin);
			if (i < item.length - 1)
				result.append(", ");
		}
		result.append("], ");
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

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			for (BinItem v : item) 
				v.bin.weight++;
					for (Var v : load) 
						v.weight++;
		}
	}	


	boolean no_sum(int[] X, int alpha, int beta)  {

		if ( alpha <= 0 || beta >= sum(X) )
			return false;

		int sum_a = 0,
				sum_b = 0,
				sum_c = 0,
				k = 0,
				kPrime = 0,
				N = X.length - 1; // |X|

		while (sum_c + X[N - kPrime] < alpha) {
			sum_c += X[N - kPrime];
			kPrime += 1;
		}
		// 	System.out.println("sum_c = " + sum_c + " k' = " + kPrime);

		sum_b = X[N - kPrime];
		while (sum_a < alpha && sum_b <= beta) {
			// 	    System.out.println(sum_a +" < " +alpha + "  "+sum_b + " <= " + beta);
			// k += 1;  // error in the original paper? moved after next instruction.
			sum_a += X[k];
			k += 1;  // error in the original paper?
			if (sum_a < alpha) {
				kPrime -= 1;
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

	int sum (int[] x) {
		int summa=0;
		for (int v : x)
			summa += v;
				return summa;
	}

	int lbBins(int[] X, int C) {

		int sum = sum(X);
		int lb = sum/C + ((sum % C !=0) ? 1 : 0);

		int[] N = new int[3];

		for (int K=0;  K <= C/2; K++) {
			for (int i=0; i < N.length; i++)
				N[i] = 0;

			int i = 0;
			while (i < X.length && X[i] > C - K) {
				N[0] += 1;
				i += 1;
			}

			int freeSpaceN1 = 0;
			while (i < X.length && X[i] > C/2) {
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
			int noBinsN2=0;
			if ( toPack > 0)
				noBinsN2 = toPack/C + ((toPack%C > 0) ? 1 : 0);

			int currentLb = N[0] + N[1] + noBinsN2;

			if (currentLb > lb)
				lb = currentLb;

		}
		return lb;
	}

	class WeightComparator<T extends BinItem> implements Comparator<T> {

		WeightComparator() {}

		public int compare(T o1, T o2) {
			return (o2.weight - o1.weight);
		}
	}

}
