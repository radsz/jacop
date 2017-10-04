/**
 * Subcircuit.java
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

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Subcircuit constraint assures that all variables build a 
 * subcircuit. Value of every variable x[i] points to the next variable in 
 * the subcircuit. If a variable does not belong to a subcircuit it has value of 
 * its position, i.e., x[i] = i.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.4
 */

public class Subcircuit extends Alldiff {

    static AtomicInteger idNumber = new AtomicInteger(0);

    Store store;

    boolean firstConsistencyCheck = true;

    int idd = 0;

    int sccLength = 0;

    int[] val;

    Hashtable<Var, Integer> valueIndex = new Hashtable<Var, Integer>();

    int firstConsistencyLevel;

    /**
     * It constructs a circuit constraint.
     * @param list variables which must form a circuit.
     */
    public Subcircuit(IntVar[] list) {

        checkInputForNullness("list", list);
        checkInputForDuplication("list", list);

        this.numberId = idNumber.incrementAndGet();
        this.list = Arrays.copyOf(list, list.length);

        this.queueIndex = 2;

        // listAlldiff = Arrays.copyOf(list, list.length);

        // min = new int[list.length];
        // max = new int[list.length];
        // u = new int[list.length];

        int i = 0;
        for (Var v : list)
            valueIndex.put(v, i++);

        val = new int[list.length];

	stack = new int[list.length];
	stack_pointer = 0;	

        setScope(list);
    }

    /**
     * It constructs a circuit constraint.
     * @param list variables which must form a circuit.
     */
    public Subcircuit(List<IntVar> list) {
        this(list.toArray(new IntVar[list.size()]));
    }


    @Override public void consistency(Store store) {

        if (firstConsistencyCheck) {
            for (int i = 0; i < list.length; i++)
                list[i].domain.in(store.level, list[i], 1, list.length);

            firstConsistencyCheck = false;
            firstConsistencyLevel = store.level;

        }

        do {

            store.propagationHasOccurred = false;

            LinkedHashSet<IntVar> fdvs = variableQueue;
            variableQueue = new LinkedHashSet<IntVar>();

            alldifferent(store, fdvs);

        } while (store.propagationHasOccurred);

        sccsBasedPruning(store); // strongly connected components

    }

    void alldifferent(Store store, LinkedHashSet<IntVar> fdvs) {

        for (IntVar changedVar : fdvs) {
            if (changedVar.singleton()) {
                for (IntVar var : list)
                    if (var != changedVar)
                        var.domain.inComplement(store.level, var, changedVar.min());
            }
        }

    }

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return IntDomain.ANY;
    }

    // registers the constraint in the constraint store
    @Override public void impose(Store store) {

        this.store = store;

        super.impose(store);

    }

    @Override public boolean satisfied() {

        if (grounded.value() != list.length)
            return false;

        boolean sat = super.satisfied(); // alldifferent

        if (sat) {
            // check if there are subcricuits that together cover all nodes
            sat = sccs(store) == list.length;
        }
        return sat;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : subcircuit([");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }
        result.append("])");

        return result.toString();
    }

    // --- Strongly Connected Conmponents

    // Uses Trajan's algorithm to find strongly connected components
    // Based on the algorithm from the book
    // Robert Sedgewick, Algorithms, 1988, p. 482.

    int[] stack;  // stack for strongly connected compoents algorithm
    int stack_pointer;
    
    BitSet cycleVar;
    
    int numberGround = 0;

    private void sccsBasedPruning(Store store) {

        // System.out.println ("========= SCCS =========");

        int maxCycle = 0;

        Arrays.fill(val, 0);

        idd = 0;
	boolean realCycle = false;
	
        for (int i = 0; i < list.length; i++) {

            sccLength = 0;

            if (val[i] == 0) {

                // System.out.print("Node " + i + ": cycle = " );

                visit(i);

                maxCycle = (sccLength > maxCycle) ? sccLength : maxCycle;
                //sccList.add(cycleVar);

                // System.out.println (cycleVar + " cycle length = " + sccLength);

                if (sccLength == 1)
                    // the scc is of size one => it must be self-cycle
                    list[i].domain.in(store.level, list[i], i + 1, i + 1);
                else {
		    // check if more than 1 sub-cycle possible
		    for (int cv = cycleVar.nextSetBit(0); cv >= 0; cv = cycleVar.nextSetBit(cv + 1)) {
			if (!list[cv].domain.contains(cv+1))
			    if (realCycle) // second sub-cycle under creation -> wrong!
				throw store.failException;
			    else {
				realCycle = true;
				break;
			    }
		    }
		    
		    if (sccLength == numberGround && numberGround < list.length) {
			// subcircuit alrerady found => all others must be self-cycles
			for (int j = 0; j < list.length; j++) {
			    if (!cycleVar.get(j))
				list[j].domain.in(store.level, list[j], j + 1, j + 1);
			}
		    }
		}
            }
        }

        int possibleSelfCycles = 0;
        for (int j = 0; j < list.length; j++)
            if (list[j].domain.contains(j + 1))
                possibleSelfCycles++;

        if (sccLength != 1 && list.length - possibleSelfCycles > maxCycle)
            // maximal cycle is smaller than possible; that is all nodes minus **possible** self-cycles
            throw Store.failException;
    }


    private int sccs(Store store) {

        // System.out.println ("========= SCCS =========");

        int totalNodes = 0;

        Arrays.fill(val, 0);

        idd = 0;

        for (int i = 0; i < list.length; i++) {

            sccLength = 0;

            if (val[i] == 0) {

                visit(i);

                totalNodes += sccLength;

                // System.out.println (cycleVar + " cycle length = " + sccLength);

            }
        }

        return totalNodes;
    }

    private int visit(int k) {

        idd++;
        val[k] = idd;
        int min = idd;

	// stack push
	stack[stack_pointer++] = k;

        for (ValueEnumeration e = list[k].domain.valueEnumeration(); e.hasMoreElements(); ) {

            int t = e.nextElement() - 1;

	    int m;
            if (val[t] == 0)
                m = visit(t);
            else 
                m = val[t];
            if (m < min) 
                min = m;
        }

        if (min == val[k]) {

            cycleVar = new BitSet(list.length); 
            numberGround = 0;

            sccLength = 0;

            int n;
            do {
		// stack pop
		n = stack[--stack_pointer];
                cycleVar.set(n);

                if (list[n].singleton())
                    numberGround++;

                val[n] = list.length + 1;

                sccLength++;
            } while (n != k);
        }

        return min;
    }
}
