/**
 * SimpleHashSet.java
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

package org.jacop.util;

import java.util.ArrayList;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.BitSet;
import java.util.Arrays;

/*
 * The implementation of the algorithm for finding dominators (simple version) in a directed graph based on 
 * Lengauer and Tarjan algorithm based on paper "A Fast Algorithm for Finding Dominators in a Flowgraph", 
 * ACM Trans. on Programming Languages and Systems, vol. 1, no. 1, July 1979.
 */
public class LengauerTarjan {

    final static int NIL = -1;

    int root;
    // succ stores successors of a vertex. Numbered from 0.
    BitSet[] succ;
    int[] parent, ancestor, vertex;
    int[] label, semi;
    BitSet[] pred, bucket;
    
    int n;  // number of nodes
    int dfs_n;

    int[] dom;

    BitSet[] domTreeSucc;    
    BitSet[] domClosure;
    
    public LengauerTarjan(int n) {
	succ = new BitSet[n];
	parent = new int[n];
	ancestor = new int[n];
	vertex = new int[n];
	label = new int[n];
	semi = new int[n];
	pred = new BitSet[n];
	bucket = new BitSet[n];
	dom = new int[n];
	
	domTreeSucc = new BitSet[n];
	domClosure = new BitSet[n];
	
	this.n = n;

	for (int i = 0; i < n; i++) {
	    succ[i] = new BitSet(n);
	    pred[i] = new BitSet(n);
	    bucket[i] = new BitSet(n);
	    
	    domTreeSucc[i] = new BitSet(n);
	}
    }

    public void init() {
	for (int i = 0; i < n; i++) {
	    succ[i].clear();
	    pred[i].clear();
	    bucket[i].clear();
	    
	    domTreeSucc[i].clear();
	}	
    }
    
    public boolean dominators(int r) {

	root = r;

	// step_1:
	Arrays.fill(semi, NIL);
	
	dfs_n = 0;
	dfs(r);

	if (dfs_n != n)
	    return false;
	
	for (int i = n-1; i > 0; i--) {

	    int w = vertex[i];
	    
	    // step_2:
	    BitSet pw = pred[w];
	    for (int v = pw.nextSetBit(0); v >= 0; v = pw.nextSetBit(v + 1)) {
		int u = eval(v);
		if (semi[u] < semi[w])
		    semi[w] = semi[u];
	    }
	    bucket[vertex[semi[w]]].set(w);
		
	    link(parent[w], w);

	    // step_3:
	    BitSet bs = bucket[parent[w]];
	    for (int v = bs.nextSetBit(0); v >= 0; v = bs.nextSetBit(v + 1)) {
		int u = eval(v);
		dom[v] = (semi[u] < semi[v]) ? u : parent[w];
	    }
	    bs.clear();
	}
	// step_4:
	for (int i = 1; i < n; i++) {
	    int w = vertex[i];
	    if (dom[w] != vertex[semi[w]])
		dom[w] = dom[dom[w]];

	    // add arc to domination tree
	    if (dom[w] != w)
	    	domTreeSucc[dom[w]].set(w);
	}
	    
	dom[r] = r;

	transitiveClosure();
	
	return true;
    }
    
    private void dfs(int v) {

	semi[v] = dfs_n;
	vertex[dfs_n] = v;
	label[v] = v;
	ancestor[v] = NIL;

	dfs_n++;
	
	BitSet sc = succ[v];
	for (int w = sc.nextSetBit(0); w >= 0; w = sc.nextSetBit(w + 1)) {
	    if (semi[w] == NIL) {
		parent[w] = v;
		dfs(w);
	    }
	    pred[w].set(v);
	}
    }

    private void compress(int v) {
	if (ancestor[ancestor[v]] != NIL) {
	    compress(ancestor[v]);
	    if (semi[label[ancestor[v]]] < semi[label[v]])
		label[v] = label[ancestor[v]];
	    ancestor[v] = ancestor[ancestor[v]];
	}
    }

    private int eval(int v) {
	if (ancestor[v] == NIL)
	    return v;
	else {
	    compress(v);
	    return label[v];
	}
    }

    private void link(int v, int w) {
	ancestor[w] = v;
    }
    
    // To add edge from u to v
    public void addArc(int u, int v) {
	succ[u].set(v);
    }

    /*
    * @param n1 graph node to be checked if it is dominated by n2
    * @param n2 graph node to be checked if it dominates n1
    * @return true : n1 is dominated by n2
    */
    public boolean dominatedBy(int n1, int n2) {
	return domClosure[n1].get(n2);	
	
	// if (dom[n1] == n2 || dom[dom[n1]] == n2)   // check only two intermediate dominators (does not need to calla transitiveClosure() first)
	//     return true;
	// else
	//     return false;
	
	// return dom[n1] == n2;  // check only intermediate dominator (does not need to calla transitiveClosure() first)
    }

    public void transitiveClosure() {
	BitSet rs = new BitSet(n);
	transitiveClosure(root, rs);
    }

    public void transitiveClosure(int v, BitSet closure) {
	closure.set(v);
	domClosure[v] = closure;

	BitSet next = domTreeSucc[v];
	for (int i = next.nextSetBit(0); i >= 0; i = next.nextSetBit(i + 1))
	    transitiveClosure(i, (BitSet)closure.clone());
    }

    public void generate(String filename) {

	FileOutputStream out; // declare a file output object
	PrintStream p; // declare a print stream object
	
	try
	    {
		// Create a new file output stream
		// connected to "myfile.txt"

		String filenameExt = filename + ".dot";
		out = new FileOutputStream(filenameExt);

		// Connect print stream to the output stream
		p = new PrintStream( out );
		
		p.print ("digraph ");
		p.print (filename);
		p.println (" {");
		p.println ("graph [  fontsize = 14,");
	        p.println ("size = \"5,5\" ];");
		p.println ("fontsize = 12");
		p.println ("size = \"5,5\";");

		printGraph(p, domTreeSucc);

		p.println ("}");

		p.close();
	    }
	catch (Exception e)
	    {
		System.err.println ("Error writing to file");
	    }
    }

    void printGraph(PrintStream p, BitSet[] successor) {
	p.println ("{");
	
	for (int i = 0; i < successor.length; i++) {
	    
	    for (int node = successor[i].nextSetBit(0); node >= 0; node = successor[i].nextSetBit(node + 1)) {
		String  arc = "\"";
		arc += i;
		arc +=  "\" -> ";
		arc +=  "\"";
		arc += node;
		arc +=  "\"";
		p.println(arc);
	    }
	}
	p.println ("}");
    }
}
