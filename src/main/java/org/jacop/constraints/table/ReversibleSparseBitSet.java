/**
 * ReversibleSparseBitSet.java
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


package org.jacop.constraints.table;

import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.IntVar;

/**
 * ReversibleSparseBitSet implements the main data structure for table constraint.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class ReversibleSparseBitSet  {

    TimeStamp<Long>[] words;
    private int[] index;
    private TimeStamp<Integer> limit;
    private long[] mask;
    
    public ReversibleSparseBitSet() {
    }

    @SuppressWarnings("unchecked")
    public ReversibleSparseBitSet(Store store, IntVar[] x, int[][] tuple) {

	int n = tuple.length;
	int lastWordSize = n % 64;
	int numberBitSets = n / 64 + ( (lastWordSize != 0) ? 1 : 0);

	limit = new TimeStamp<Integer>(store, numberBitSets-1);
	words = new TimeStamp[numberBitSets];
	
	long[] bs = new long[numberBitSets];
	for (int i = 0; i < tuple.length; i++) 
	    if (validTuple(x, tuple[i])) 
		setBit(i, bs);

	for (int i = 0; i < numberBitSets; i++) 
	    words[i] = new TimeStamp<Long>(store, bs[i]);
	
	index = new int[numberBitSets];
	for (int i = 0; i < numberBitSets; i++) 
	    index[i] = i;

	mask = new long[numberBitSets];
    }

    private long[] setBit(int n, long[] a) {

	int l = n % 64;
	int m = n / 64;

	a[m] |= (1L << l);
	
	return a;
    }

    private boolean validTuple(IntVar[] x, int[] t) {

	int n = t.length;
	int i=0;
	while (i < n) {
	    if (!x[i].dom().contains(t[i]))
		return false;
	    i++;
	}
	return true;
    }	
	
    boolean isEmpty() {
	return limit.value() == -1;
    }

    void clearMask() {
	for (int i = 0; i < limit.value()+1; i++) {
	    int offset = index[i];
	    mask[offset] = 0;
	}
    }

    void reverseMask() {
	for (int i = 0; i < limit.value()+1; i++) {
	    int offset = index[i];
	    mask[offset] = ~ mask[offset];
	}
    }

    void addToMask(long[] m) {
	for (int i = 0; i < limit.value()+1; i++) {
	    int offset = index[i];
	    mask[offset] = mask[offset] | m[offset];
	}		
    }

    void intersectWithMask() {

	for (int i = limit.value(); i >= 0; i--) {
	    int offset = index[i];
	    long wOriginal = words[offset].value();
	    long w = wOriginal;

	    w &= mask[offset];

	    if (w != wOriginal) {
		words[offset].update(w);
		if (w == 0) {
		    int l = limit.value();
		    index[i] = index[l];
		    index[l] = offset;
		    limit.update(l-1);
		}
	    }
	}
    }

    int intersectIndex(long[] m) {

	for (int i = 0; i < limit.value()+1; i++) {
	    int offset = index[i];
	    long w = words[offset].value();

	    w &= m[offset];
	    if (w != 0)
		return offset;
	}
	return -1;
    }


    int noWords() {
	return words.length;
    }
    
    public String toString() {
	StringBuffer s = new StringBuffer("words: ");

	int n = limit.value()+1;
	s.append("limit = " + (n-1) +"\n");
	for (int i = 0; i < n; i++) {
	    int offset = index[i];
	    s.append(offset+": ");
	    s.append(String.format("0x%08X", words[offset].value()));
	    if ( i < n-1)
		s.append(", ");
	}	

	s.append("\nmask: ");
	for (int i = 0; i < mask.length; i++) {
	    s.append(i+": ");
	    s.append(String.format("0x%08X", mask[i])+", ");
	}
	return s.toString();
    }
}
