/**
 *  Subcircuit.java 
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.LinkedHashSet;
import java.util.Stack;

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
 * @version 4.2
 */

public class Subcircuit extends Alldiff {

    Store store;

    boolean firstConsistencyCheck = true;

    int idd = 0;

    int sccLength = 0;

    int[] val;

    static int IdNumber = 0;
	
    Hashtable<Var, Integer> valueIndex = new Hashtable<Var, Integer>();

    int firstConsistencyLevel;

    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"list"};

    /**
     * It constructs a circuit constraint.
     * @param list variables which must form a circuit.
     */
    public Subcircuit(IntVar[] list) {

	super(list);

	Alldiff.idNumber--;
	numberId = IdNumber++;

	int i = 0;
	for (Var v : list)
	    valueIndex.put(v, i++);

	val = new int[list.length];
    }

    /**
     * It constructs a circuit constraint.
     * @param list variables which must form a circuit.
     */
    public Subcircuit(ArrayList<IntVar> list) {

	this(list.toArray(new IntVar[list.size()]));
    }


    @Override
	public void consistency(Store store) {

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

    // registers the constraint in the constraint store
    @Override
	public void impose(Store store) {

	this.store = store;

	super.impose(store);

    }


    @Override
	public boolean satisfied() {
		
	if (grounded.value() != list.length)
	    return false;
		
	boolean sat = super.satisfied(); // alldifferent

	if (sat) {
	    // check if there are subcricuits that together cover all nodes
	    sat = sccs(store) == list.length;
	}
	return sat;
    }

    @Override
	public String toString() {
		
	StringBuffer result = new StringBuffer( id() );
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
    // if found strongly connected component is shorter than the
    // Hamiltonian circuit length fail is enforced (one is unable to
    // to build a circuit. Based on the algorithm from the book
    // Robert Sedgewick, Algorithms, 1988, p. 482.

    Stack<Integer> stck = new Stack<Integer>();

    ArrayList<IntVar> cycleVar;

    int numberGround = 0;

    void sccsBasedPruning(Store store) {

	// System.out.println ("========= SCCS =========");

	int maxCycle = 0;

	//ArrayList<ArrayList<IntVar>> sccList = new ArrayList<ArrayList<IntVar>>();

	// for (int i = 0; i < val.length; i++)
	//     val[i] = 0;
	java.util.Arrays.fill(val, 0);

	idd = 0;

 	for (int i=0; i< list.length; i++) {

 	    sccLength = 0;

 	    if (val[i] == 0) {

 		// System.out.print("Node " + i + ": cycle = " );

		visit(i);

		maxCycle = (sccLength > maxCycle) ? sccLength : maxCycle;
		//sccList.add(cycleVar);

		// System.out.println (cycleVar + " cycle length = " + sccLength);

		if (sccLength == 1) 
		    // the scc is of size one => it must be self-cycle		
		    list[i].domain.in(store.level, list[i], i+1, i+1);

		else if (sccLength == numberGround && numberGround < list.length) {
		    // subcircuit alrerady found => all others must be self-cycles
		    for (int j=0; j<list.length; j++) {
			if ( !cycleVar.contains(list[j]) ) 
			    list[j].domain.in(store.level, list[j], j+1, j+1);
		    }
		}
	    }
	}

	int possibleSelfCycles = 0;
	for (int j=0; j<list.length; j++) 
	    if (list[j].domain.contains(j+1))
		possibleSelfCycles++;

	if (sccLength != 1 && list.length - possibleSelfCycles > maxCycle) 
	    // maximal cycle is smaller than possible; that is all nodes minus **possible** self-cycles
	    throw Store.failException;

	/*
	// check for a cycle with a single non ground variable and ground it to form the cycle
	for (ArrayList<IntVar> scc : sccList) {

	IntVar nonGround = null;
	IntDomain cycleNodes = new IntervalDomain();
	int numberGround = 0;

	for (IntVar c : scc) {

	if (c.singleton())
	numberGround++;
	else
	nonGround = c;

	cycleNodes.unionAdapt(valueIndex.get(c)+1, valueIndex.get(c)+1);
	}

	if (numberGround + 1 == scc.size()) 
	nonGround.domain.in(store.level, nonGround, cycleNodes);
	}
	*/

    }


    int sccs(Store store) {

	// System.out.println ("========= SCCS =========");

	int totalNodes = 0;

	// for (int i = 0; i < val.length; i++)
	//     val[i] = 0;
	java.util.Arrays.fill(val, 0);

	idd = 0;

 	for (int i=0; i< list.length; i++) {

 	    sccLength = 0;

 	    if (val[i] == 0) {

 		// System.out.print("Node " + i + ": cycle = " );

		visit(i);

		totalNodes += sccLength;

		// System.out.println (cycleVar + " cycle length = " + sccLength);

	    }
	}

	return totalNodes;
    }

    int visit(int k) {

	int m, min = 0, t;
	idd++;
	val[k] = idd;
	min = idd;

    	stck.push(k);

	for (ValueEnumeration e = list[k].dom().valueEnumeration(); e.hasMoreElements();) {

	    t = e.nextElement() - 1;
	    if (val[t] == 0)
		m = visit(t);
	    else
		m = val[t];
	    if (m < min)
		min = m;
	}

	if (min == val[k]) {

	    // System.out.print("SCC: ");

	    int n;
	    cycleVar = new ArrayList<IntVar>();
	    numberGround=0;

	    sccLength = 0;

	    do {
		n = stck.pop();
		cycleVar.add(list[n]);

		if (list[n].singleton())
		    numberGround++;

		val[n] = list.length + 1;

		sccLength++;
	    } while ( n != k);

	    // System.out.println ("cycleVar = " + cycleVar + ", ground = " + numberGround);

	}
	return min;
    }
	
}
