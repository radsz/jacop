/**
 * GlobalConstraints.java
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
package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.HashSet;

import org.jacop.core.Store;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.IntDomain;
import org.jacop.core.Var;

import org.jacop.set.core.SetVar;

import org.jacop.fz.*;

import org.jacop.set.constraints.AdisjointB;

import org.jacop.constraints.XeqC;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.Or;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.SoftAlldifferent;
import org.jacop.constraints.ViolationMeasure;
import org.jacop.constraints.SoftGCC;
import org.jacop.constraints.AmongVar;
import org.jacop.constraints.Among;
import org.jacop.constraints.GCC;
import org.jacop.constraints.Values;
import org.jacop.constraints.Count;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ExtensionalSupportMDD;
import org.jacop.constraints.ExtensionalSupportSTR;
import org.jacop.constraints.Assignment;
import org.jacop.util.fsm.FSMTransition;
import org.jacop.util.fsm.FSM;
import org.jacop.util.fsm.FSMState;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Sequence;
import org.jacop.constraints.Stretch;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.ValuePrecede;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.NetworkFlow;
import org.jacop.constraints.Constraint;
import org.jacop.floats.core.FloatVar;
import org.jacop.constraints.geost.Geost;
import org.jacop.constraints.geost.ExternalConstraint;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.geost.NonOverlapping;
import org.jacop.constraints.geost.InArea;
import org.jacop.constraints.geost.DBox;
import org.jacop.constraints.geost.Shape;

/**
 *
 * Generation of global constraints in flatzinc
 *
 * @author Krzysztof Kuchcinski 
 *
 */
class GlobalConstraints implements ParserTreeConstants {

    Store store;
    Support support;    

    boolean useDisjunctions = false;
    boolean useCumulativeUnary = false;
    
    public GlobalConstraints(Support support) {
	this.store = support.store;
	this.support = support;
    }

    void gen_jacop_cumulative(SimpleNode node) {

	// possible to control when edge find algorithm is used for Cumulative constraint
	// System.setProperty("max_edge_find_size", "10");
	
        IntVar[] str = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] dur = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        IntVar[] res = support.getVarArray((SimpleNode) node.jjtGetChild(2));
        IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

        // Filter non-existing tasks
        ArrayList<IntVar> start = new ArrayList<IntVar>();
        ArrayList<IntVar> duration = new ArrayList<IntVar>();
        ArrayList<IntVar> resource = new ArrayList<IntVar>();
        for (int i = 0; i < str.length; i++) {
            if (!res[i].singleton(0) && !dur[i].singleton(0)) {
                start.add(str[i]);
                duration.add(dur[i]);
                resource.add(res[i]);
            }
        }

        IntVar[] s = start.toArray(new IntVar[start.size()]);
        IntVar[] d = duration.toArray(new IntVar[duration.size()]);
        IntVar[] r = resource.toArray(new IntVar[resource.size()]);

	/* !!! IMPORTANT !!!  Cumulative constraint is added after all other constraints are posed since
	 * it has expensive consistency method that do not need to be executed during model
	 * initialization every time an added constraint triggers execution of Cumulative.
	 */
	
        if (s.length == 0)
            return;
        else if (s.length == 1)
            support.pose(new XlteqY(r[0], b));
        else if (b.max() == 1)  // cumulative unary
            support.delayedConstraints.add(new CumulativeUnary(s, d, r, b, true));
        else {
            int min = Math.min(r[0].min(), r[1].min());
            int nextMin = Math.max(r[0].min(), r[1].min());
            for (int i = 2; i < r.length; i++) {
                if (r[i].min() < min) {
                    nextMin = min;
                    min = r[i].min();
                } else if (r[i].min() < nextMin) {
                    nextMin = r[i].min();
                }
            }
            boolean unaryPossible = (min > b.max() / 2) || (nextMin > b.max() / 2 && min + nextMin > b.max());
            if (unaryPossible) {
                if (allVarOne(d)) {
                    support.pose(new Alldiff(s));
                    if (!b.singleton())
                        for (int i = 0; i < r.length; i++)
                            support.pose(new XlteqY(r[i], b));
                } else // possible to use CumulativeUnary (it is used with profile propagator; option true)
		    support.delayedConstraints.add(new CumulativeUnary(s, d, r, b, true));
                // these constraints are not needed if we run with profile-based propagator
                // for (int i = 0; i < r.length; i++)
                //   support.pose(new XlteqY(r[i], b));
            } else if (allVarGround(d) && allVarGround(r)) {
		HashSet<Integer> diff = new HashSet<Integer>();
		for (IntVar e : r) 
		    diff.add(e.min());
		double n = (double)r.length;
		double k = (double)diff.size();
		// KKU, 2017-04-05, formula when 3.5*n*n < n*k*log(n),
		// where 3.5 is experimantally selected constant
		if (3.5*n*n < n*k*Math.log10((double)n)/Math.log10(2.0))
		    // complexity O(n^2)
		    support.delayedConstraints.add(new org.jacop.constraints.Cumulative(s, d, r, b, true, true, false));
		else
		    // complexity O(n*k*logn)
		    support.delayedConstraints.add(new Cumulative(s, d, r, b));

		String p = System.getProperty("fz_cumulative_use_disjunctions");
		if (p != null) 
		    useDisjunctions = Boolean.parseBoolean(p);
		p = System.getProperty("fz_cumulative_use_unary");
		if (p != null) 
		    useCumulativeUnary = Boolean.parseBoolean(p);

		if (useCumulativeUnary)
		    impliedCumulativeUnaryConstraints(s, d, r, b);
		if (useDisjunctions)
		    impliedDisjunctionConstraints(s, d, r, b);
            } else {
                support.delayedConstraints.add(new CumulativeBasic(s, d, r, b));

		String p = System.getProperty("fz_cumulative_use_disjunctions");
		if (p != null) 
		    useDisjunctions = Boolean.parseBoolean(p);
		p = System.getProperty("fz_cumulative_use_unary");
		if (p != null) 
		    useCumulativeUnary = Boolean.parseBoolean(p);

		if (useCumulativeUnary)
		    impliedCumulativeUnaryConstraints(s, d, r, b);
		if (useDisjunctions)
		    impliedDisjunctionConstraints(s, d, r, b);
	    }
        }
    }

    void impliedCumulativeUnaryConstraints(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {

	int limit = b.max()/2 + 1;

	ArrayList<IntVar> start = new ArrayList<IntVar>();
	ArrayList<IntVar> dur = new ArrayList<IntVar>();
	ArrayList<IntVar> res = new ArrayList<IntVar>();
	
	for (int i = 0; i < r.length; i++) {
	    if (r[i].min() >= limit) {
		start.add(s[i]);
		dur.add(d[i]);
		res.add(r[i]);
	    }
	}
	// use CumulativeUnary for tasks that have resource capacity greater than half of the cumulative capacity bound.
	if (start.size() > 1)
	    support.delayedConstraints.add(new CumulativeUnary(start, dur, res, b, false));
    }
    
    void impliedDisjunctionConstraints(IntVar[] s, IntVar[] d, IntVar[] r, IntVar b) {
	
	// use pairwaise task disjunction constraints for all pairs of tasks that have sum of resource capacities
	// greater than the cumulative capacity bound.
	for (int i = 0; i < s.length; i++) {
	    for (int j = i+1; j < s.length; j++) {
		if (r[i].min() + r[j].min() > b.max()) {
		    if (d[i].singleton() && d[j].singleton())
			support.pose(new Or(new XplusClteqZ(s[i], d[i].value(), s[j]),
					    new XplusClteqZ(s[j], d[j].value(), s[i])));
		    else 
			support.pose(new Or(new XplusYlteqZ(s[i], d[i], s[j]),
					    new XplusYlteqZ(s[j], d[j], s[i])));
		}
	    }
	}
    }

    void gen_jacop_circuit(SimpleNode node) {
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));

        support.pose(new Circuit(v));

        if (support.domainConsistency && !support.options.getBoundConsistency())  // we add additional implied constraint if domain consistency is required
            support.parameterListForAlldistincts.add(v);
    }

    void gen_jacop_subcircuit(SimpleNode node) {
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        support.pose(new Subcircuit(v));

	if (support.domainConsistency && !support.options.getBoundConsistency())  // we add additional implied constraint if domain consistency is required
            support.parameterListForAlldistincts.add(v);
}

    void gen_jacop_alldiff(SimpleNode node) {
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));

        IntervalDomain dom = new IntervalDomain();
        for (IntVar var : v)
            dom = (IntervalDomain) dom.union(var.dom());
        if (v.length <= 100) { // && v.length == dom.getSize()) {
            // we do not not pose Alldistinct directly because of possible inconsistency with its
            // intiallization; we collect all vectors and pose it at the end when all constraints are posed
            // support.pose(new Alldistinct(v));

            if (support.boundsConsistency || support.options.getBoundConsistency()) {
                support.pose(new Alldiff(v));
                // System.out.println("Alldiff imposed");
            } else { // domain consistency
                support.parameterListForAlldistincts.add(v);
            }
        } else {
            support.pose(new Alldiff(v));
        }
    }

    void gen_jacop_softalldiff(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar s = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        int useDecomp = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        // 0 if false, 1 if true
        ViolationMeasure usedMeasure = (useDecomp == 0) ? ViolationMeasure.VARIABLE_BASED : ViolationMeasure.DECOMPOSITION_BASED;
        SoftAlldifferent sa = new SoftAlldifferent(x, s, usedMeasure);
        // sa.primitiveDecomposition(store);
        support.poseDC(sa);
    }

    void gen_jacop_softgcc(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        int[] values = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        IntVar[] hard_counters = support.getVarArray((SimpleNode) node.jjtGetChild(2));
        IntVar[] soft_counters = support.getVarArray((SimpleNode) node.jjtGetChild(3));
        IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(4));

        SoftGCC sgcc = new SoftGCC(x, hard_counters, values, soft_counters, cost, ViolationMeasure.VALUE_BASED);
        //sgcc.primitiveDecomposition(store);
        support.poseDC(sgcc);
    }

    void gen_jacop_alldistinct(SimpleNode node) {
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        // we do not not pose Alldistinct directly because of possible inconsistency with its
        // intiallization; we collect all vectors and pose it at the end when all constraints are posed

        support.parameterListForAlldistincts.add(v);
    }

    void gen_jacop_among_var(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] s = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

        // we do not not pose AmongVar directly because of possible inconsistency with its
        // intiallization; we collect all constraints and pose them at the end when all other constraints are posed

        // ---- KK, 2015-10-17
        // among must not have duplicated variables there
        // could be constants that have the same value and
        // are duplicated.
        IntVar[] xx = new IntVar[x.length];
        HashSet<IntVar> varSet = new HashSet<IntVar>();
        for (int i = 0; i < x.length; i++) {
            if (varSet.contains(x[i]) && x[i].singleton())
                xx[i] = new IntVar(store, x[i].min(), x[i].max());
            else {
                xx[i] = x[i];
                varSet.add(x[i]);
            }
        }
        IntVar[] ss = new IntVar[s.length];
        varSet = new HashSet<IntVar>();
        for (int i = 0; i < s.length; i++) {
            if (varSet.contains(s[i]) && s[i].singleton())
                ss[i] = new IntVar(store, s[i].min(), s[i].max());
            else {
                ss[i] = s[i];
                varSet.add(s[i]);
            }
        }
        IntVar vv;
        if (varSet.contains(v) && v.singleton())
            vv = new IntVar(store, v.min(), v.max());
        else
            vv = v;

        support.delayedConstraints.add(new AmongVar(xx, ss, vv));
        // 		    support.pose(new AmongVar(x, s, v));
    }

    void gen_jacop_among(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntDomain s = support.getSetLiteral(node, 1);
        IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

        // ---- KK, 2015-10-17
        // among must not have duplicated variables. In x vecor
        // could be constants that have the same value and
        // are duplicated.
        IntVar[] xx = new IntVar[x.length];
        HashSet<IntVar> varSet = new HashSet<IntVar>();
        for (int i = 0; i < x.length; i++) {
            if (varSet.contains(x[i]) && x[i].singleton())
                xx[i] = new IntVar(store, x[i].min(), x[i].max());
            else {
                xx[i] = x[i];
                varSet.add(x[i]);
            }
        }
        IntVar vv;
        if (varSet.contains(v) && v.singleton())
            vv = new IntVar(store, v.min(), v.max());
        else
            vv = v;

        IntervalDomain setImpl = new IntervalDomain();
        for (ValueEnumeration e = s.valueEnumeration(); e.hasMoreElements(); ) {
            int val = e.nextElement();

            setImpl.unionAdapt(new IntervalDomain(val, val));
        }

        support.pose(new Among(xx, setImpl, vv));
    }

    void gen_jacop_gcc(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] c = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        int index_max = index_min + c.length - 1;

        for (int i = 0; i < x.length; i++) {
            if (index_min > x[i].max() || index_max < x[i].min()) {
                throw new IllegalArgumentException("%% ERROR: gcc domain error in variable " + x[i]);
            }
            if (index_min > x[i].min() && index_min < x[i].max())
                x[i].domain.inMin(store.level, x[i], index_min);
            if (index_max < x[i].max() && index_max > x[i].min())
                x[i].domain.inMax(store.level, x[i], index_max);
        }
        // 		    System.out.println("c = " + Arrays.asList(x));

        // =========> remove all non-existing-values counters
        IntDomain gcc_dom = new IntervalDomain();
        for (IntVar v : x)
            gcc_dom = gcc_dom.union(v.dom());
        ArrayList<Var> c_list = new ArrayList<Var>();
        for (int i = 0; i < c.length; i++)
            if (gcc_dom.contains(i + index_min))
                c_list.add(c[i]);
            else
                support.pose(new XeqC(c[i], 0));
        IntVar[] c_array = new IntVar[c_list.size()];
        c_array = c_list.toArray(c_array);
        // =========>

        support.pose(new GCC(x, c_array));
    }

    void gen_jacop_global_cardinality_closed(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        int[] cover = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        IntVar[] counter = support.getVarArray((SimpleNode) node.jjtGetChild(2));

        IntDomain gcc_dom = new IntervalDomain();
        for (int e : cover)
            gcc_dom = gcc_dom.union(e);
        for (IntVar v : x)
            v.domain.in(store.level, v, gcc_dom);

        support.pose(new GCC(x, counter));
    }

    void gen_jacop_global_cardinality_low_up_closed(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        int[] cover = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int[] low = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        int[] up = support.getIntArray((SimpleNode) node.jjtGetChild(3));

        IntDomain gcc_dom = new IntervalDomain();
        for (int e : cover)
            gcc_dom = gcc_dom.union(e);
        for (IntVar v : x)
            v.domain.in(store.level, v, gcc_dom);

        IntVar[] counter = new IntVar[low.length];
        for (int i = 0; i < counter.length; i++)
            counter[i] = new IntVar(store, "counter" + i, low[i], up[i]);

        support.pose(new GCC(x, counter));
    }

    void gen_jacop_diff2_strict(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        IntVar[] lx = support.getVarArray((SimpleNode) node.jjtGetChild(2));
        IntVar[] ly = support.getVarArray((SimpleNode) node.jjtGetChild(3));

        // support.pose(new Disjoint(x, y, lx, ly));
        support.pose(new Diffn(x, y, lx, ly, true));
    }

    void gen_jacop_diff2(SimpleNode node) {
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));

        IntVar[][] r = new IntVar[v.length / 4][4];
        for (int i = 0; i < r.length; i++)
            for (int j = 0; j < 4; j++)
                r[i][j] = v[4 * i + j];

        // support.pose(new Diff2(r));
        support.pose(new Diffn(r, false));
    }

    void gen_jacop_list_diff2(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        IntVar[] lx = support.getVarArray((SimpleNode) node.jjtGetChild(2));
        IntVar[] ly = support.getVarArray((SimpleNode) node.jjtGetChild(3));

        // support.pose(new Diff2(x, y, lx, ly));
        support.pose(new Diffn(x, y, lx, ly, false));
    }

    void gen_jacop_count(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        int y = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
        IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

        ArrayList<IntVar> xs = new ArrayList<IntVar>();
        for (IntVar v : x) {
            if (y >= v.min() && y <= v.max())
                xs.add(v);
        }
        if (xs.size() == 0) {
            c.domain.in(store.level, c, 0, 0);
            return;
        } else
            support.pose(new Count(xs, c, y));
    }

    void gen_jacop_nvalue(SimpleNode node) {
        IntVar n = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));

        support.pose(new Values(x, n));
    }

    void gen_jacop_minimum_arg_int(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

        support.pose(new ArgMin(x, index));
    }

    void gen_jacop_minimum(SimpleNode node) {
        IntVar n = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));

        support.pose(new org.jacop.constraints.Min(x, n));
    }

    void gen_jacop_maximum_arg_int(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

        support.pose(new ArgMax(x, index));
    }

    void gen_jacop_maximum(SimpleNode node) {
        IntVar n = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));

        support.pose(new org.jacop.constraints.Max(x, n));
    }

    void gen_jacop_table_int(SimpleNode node) {
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        int size = v.length;

	// create tuples for the constraint; remove non feasible tuples
        int[] tbl = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int[][] t = new int[tbl.length / size][size];
	boolean[] tuplesToRemove = new boolean[t.length];
	int n=0;
        for (int i = 0; i < t.length; i++) {
            for (int j = 0; j < size; j++) {
		if (! v[j].domain.contains(tbl[size * i + j])) {
		    tuplesToRemove[i] = true;
		}
                t[i][j] = tbl[size * i + j];
	    }
	    if (tuplesToRemove[i])
		n++;
	}
	int k = t.length-n;
	int[][] newT = new int[k][size];
	int m = 0;
	for (int i = 0; i < t.length; i++) 
	    if (! tuplesToRemove[i]) 
		newT[m++] = t[i];
	tbl = null;
	t = newT;
	
        int[] vu = uniqueIndex(v);
        if (vu.length != v.length) { // non unique variables

            int[][] tt = new int[t.length][vu.length];
            for (int i = 0; i < tt.length; i++)
                for (int j = 0; j < vu.length; j++)
                    tt[i][j] = t[i][vu[j]];

            IntVar[] uniqueVar = support.unique(v);
            if (uniqueVar.length == 1) {
                IntervalDomain d = new IntervalDomain();
                for (int i = 0; i < tt.length; i++)
                    d.addDom(new IntervalDomain(tt[i][0], tt[i][0]));
                uniqueVar[0].domain.in(store.level, uniqueVar[0], d);
                if (support.options.debug())
                    System.out.println(uniqueVar[0] + " in " + d);

            } else
		if (t.length <= 64)
		    support.pose(new org.jacop.constraints.table.SimpleTable(v, tt, true));
		else
		    support.pose(new org.jacop.constraints.table.Table(v, tt, true));	    
        } else
	    if (t.length <= 64)
	    	support.pose(new org.jacop.constraints.table.SimpleTable(v, t, true));
	    else
	    	support.pose(new org.jacop.constraints.table.Table(v, t, true));	    
    }

    void gen_jacop_assignment(SimpleNode node) {
        IntVar[] f = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] invf = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        int index_f = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        int index_invf = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));

        // we do not not pose Assignment directly because of possible inconsistency with its
        // intiallization; we collect all constraints and pose them at the end when all other constraints are posed

        if (support.domainConsistency && !support.options.getBoundConsistency())  // we add additional implied constraint if domain consistency is required
            support.parameterListForAlldistincts.add(f);

        support.delayedConstraints.add(new Assignment(f, invf, index_f, index_invf));
    }

    void gen_jacop_regular(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        int Q = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
        int S = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        int[] d = support.getIntArray((SimpleNode) node.jjtGetChild(3));
        int q0 = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(4));
        IntDomain F = support.getSetLiteral(node, 5);
        int minIndex = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(6));

        // Build DFA
        FSM dfa = new FSM();
        FSMState[] s = new FSMState[Q];
        for (int i = 0; i < s.length; i++) {
            s[i] = new FSMState();
            dfa.allStates.add(s[i]);
        }
        dfa.initState = s[q0 - 1];
        ValueEnumeration final_states = F.valueEnumeration(); //new SetValueEnumeration(F);
        while (final_states.hasMoreElements())
            dfa.finalStates.add(s[final_states.nextElement() - 1]);

        for (int i = 0; i < Q; i++) {
            for (int j = 0; j < S; j++)
                if (d[i * S + j] != 0) {
                    s[i].transitions.add(new FSMTransition(new IntervalDomain(j + minIndex, j + minIndex), s[d[i * S + j] - minIndex]));
                }
        }

        support.pose(new Regular(dfa, x));
    }

    void gen_jacop_knapsack(SimpleNode node) {
        int[] weights = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        int[] profits = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        IntVar W = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        IntVar P = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(4));

        support.pose(new Knapsack(profits, weights, x, W, P));
    }

    void gen_jacop_sequence(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntDomain u = support.getSetLiteral(node, 1);
        int q = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        int min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));
        int max = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(4));

        IntervalDomain setImpl = new IntervalDomain();
        for (int i = 0; true; i++) {
            Interval val = u.getInterval(i);
            if (val != null)
                setImpl.unionAdapt(val);
            else
                break;
        }

        DecomposedConstraint c = new Sequence(x, setImpl, q, min, max);
        support.poseDC(c);
    }

    void gen_jacop_stretch(SimpleNode node) {
        int[] values = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        int[] min = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int[] max = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(3));

        DecomposedConstraint c = new Stretch(values, min, max, x);
        support.poseDC(c);
    }

    void gen_jacop_disjoint(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);

        support.pose(new AdisjointB(v1, v2));
    }

    void gen_jacop_networkflow(SimpleNode node) {
        int[] arc = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] flow = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        IntVar[] weight = support.getVarArray((SimpleNode) node.jjtGetChild(2));
        int[] balance = support.getIntArray((SimpleNode) node.jjtGetChild(3));
        IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(4));

        NetworkBuilder net = new NetworkBuilder();

        org.jacop.constraints.netflow.simplex.Node[] netNode = new org.jacop.constraints.netflow.simplex.Node[balance.length];
        for (int i = 0; i < balance.length; i++)
            netNode[i] = net.addNode("n_" + i, balance[i]);

        for (int i = 0; i < flow.length; i++) {
            net.addArc(netNode[arc[2 * i] - 1], netNode[arc[2 * i + 1] - 1], weight[i], flow[i]);
        }

        net.setCostVariable(cost);

        support.pose(new NetworkFlow(net));
    }

    void gen_jacop_lex_less_int(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));

        support.pose(new LexOrder(x, y, true));
    }

    void gen_jacop_lex_lesseq_int(SimpleNode node) {
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] y = support.getVarArray((SimpleNode) node.jjtGetChild(1));

        support.pose(new LexOrder(x, y, false));
    }

    void gen_jacop_value_precede_int(SimpleNode node) {
	int s = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(0));
	int t = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1));
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(2));

	// no repeated varibales allowed in ValuePrecede and
	// we create a new vector with different variables
	IntVar[] xs = new IntVar[x.length];
        HashSet<IntVar> varSet = new HashSet<IntVar>();
        for (int i = 0; i < x.length; i++) {
            if (varSet.contains(x[i])) {
		IntVar tmp = new IntVar(store, x[i].min(), x[i].max());
		support.pose(new org.jacop.constraints.XeqY(x[i], tmp));
                xs[i] = tmp;
	    }
            else {
                xs[i] = x[i];
                varSet.add(x[i]);
            }
        }
	
	support.pose(new ValuePrecede(s, t, xs));
    }

    void gen_jacop_bin_packing(SimpleNode node) {
        IntVar[] bin = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] capacity = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        int[] w = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        int min_bin = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));

        //support.pose( new org.jacop.constraints.binpacking.Binpacking(binx, capacity, w) );
        Constraint binPack = new Binpacking(bin, capacity, w, min_bin);
        support.delayedConstraints.add(binPack);
    }

    void gen_jacop_float_maximum(SimpleNode node) {
        FloatVar p2 = support.getFloatVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        FloatVar[] p1 = support.getFloatVarArray((SimpleNode) node.jjtGetChild(0));

        support.pose(new org.jacop.floats.constraints.Max(p1, p2));
    }

    void gen_jacop_float_minimum(SimpleNode node) {
        FloatVar p2 = support.getFloatVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        FloatVar[] p1 = support.getFloatVarArray((SimpleNode) node.jjtGetChild(0));

        support.pose(new org.jacop.floats.constraints.Min(p1, p2));
    }

    void gen_jacop_geost(SimpleNode node) {
        int dim = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(0));
        int[] rect_size = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int[] rect_offset = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        IntDomain[] shape = support.getSetArray((SimpleNode) node.jjtGetChild(3));
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(4));
        IntVar[] kind = support.getVarArray((SimpleNode) node.jjtGetChild(5));

        // System.out.println("dim = " + dim);
        // System.out.print("rect_size = [");
        // for (int i = 0; i < rect_size.length; i++)
        // 	System.out.print(" " + rect_size[i]);
        // System.out.print("]\nrect_offset = [");
        // for (int i = 0; i < rect_offset.length; i++)
        // 	System.out.print(" " + rect_offset[i]);
        // System.out.println("]\nshape = " + java.util.Arrays.asList(shape));
        // System.out.println("x = " + java.util.Arrays.asList(x));
        // System.out.println("kind = " + java.util.Arrays.asList(kind));
        // System.out.println("===================");


        ArrayList<Shape> shapes = new ArrayList<Shape>();

        // dummy shape to have right indexes for kind (starting from 1)
        ArrayList<DBox> dummy = new ArrayList<DBox>();
        int[] offsetDummy = new int[dim];
        int[] sizeDummy = new int[dim];
        for (int k = 0; k < dim; k++) {
            offsetDummy[k] = 0;
            sizeDummy[k] = 1;
        }
        dummy.add(new DBox(offsetDummy, sizeDummy));
        shapes.add(new Shape(0, dummy));

        // create all shapes (starting with id=1)
        for (int i = 0; i < shape.length; i++) {
            ArrayList<DBox> shape_i = new ArrayList<DBox>();

            for (ValueEnumeration e = shape[i].valueEnumeration(); e.hasMoreElements(); ) {
                int j = e.nextElement();

                int[] offset = new int[dim];
                int[] size = new int[dim];

                for (int k = 0; k < dim; k++) {
                    offset[k] = rect_offset[(j - 1) * dim + k];
                    size[k] = rect_size[(j - 1) * dim + k];
                }
                shape_i.add(new DBox(offset, size));

            }
            shapes.add(new Shape((i + 1), shape_i));
        }

        // for (int i = 0; i < shapes.size(); i++)
        // 	System.out.println("*** " + shapes.get(i));

        ArrayList<GeostObject> objects = new ArrayList<GeostObject>();

        for (int i = 0; i < kind.length; i++) {

            IntVar[] coords = new IntVar[dim];

            for (int k = 0; k < dim; k++)
                coords[k] = x[i * dim + k];

            // System.out.println("coords = " + java.util.Arrays.asList(coords));

            IntVar start = new IntVar(store, "start[" + i + "]", 0, 0);
            IntVar duration = new IntVar(store, "duration[" + i + "]", 1, 1);
            IntVar end = new IntVar(store, "end[" + i + "]", 1, 1);
            GeostObject obj = new GeostObject(i, coords, kind[i], start, duration, end);
            objects.add(obj);
        }

        // System.out.println("===========");
        // for (int i = 0; i < objects.size(); i++)
        // 	System.out.println(objects.get(i));
        // System.out.println("===========");

        ArrayList<ExternalConstraint> constraints = new ArrayList<ExternalConstraint>();
        int[] dimensions = new int[dim + 1];
        for (int i = 0; i < dim + 1; i++)
            dimensions[i] = i;

        NonOverlapping constraint1 = new NonOverlapping(objects, dimensions);
        constraints.add(constraint1);

        support.pose(new Geost(objects, constraints, shapes));
    }

    void gen_jacop_geost_bb(SimpleNode node) {
        int dim = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(0));
        int[] rect_size = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int[] rect_offset = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        IntDomain[] shape = support.getSetArray((SimpleNode) node.jjtGetChild(3));
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(4));
        IntVar[] kind = support.getVarArray((SimpleNode) node.jjtGetChild(5));

        // System.out.println("dim = " + dim);
        // System.out.print("rect_size = [");
        // for (int i = 0; i < rect_size.length; i++)
        // 	System.out.print(" " + rect_size[i]);
        // System.out.print("]\nrect_offset = [");
        // for (int i = 0; i < rect_offset.length; i++)
        // 	System.out.print(" " + rect_offset[i]);
        // System.out.println("]\nshape = " + java.util.Arrays.asList(shape));
        // System.out.println("x = " + java.util.Arrays.asList(x));
        // System.out.println("kind = " + java.util.Arrays.asList(kind));
        // System.out.println("===================");


        ArrayList<Shape> shapes = new ArrayList<Shape>();

        // dummy shape to have right indexes for kind (starting from 1)
        ArrayList<DBox> dummy = new ArrayList<DBox>();
        int[] offsetDummy = new int[dim];
        int[] sizeDummy = new int[dim];
        for (int k = 0; k < dim; k++) {
            offsetDummy[k] = 0;
            sizeDummy[k] = 1;
        }
        dummy.add(new DBox(offsetDummy, sizeDummy));
        shapes.add(new Shape(0, dummy));

        // create all shapes (starting with id=1)
        for (int i = 0; i < shape.length; i++) {
            ArrayList<DBox> shape_i = new ArrayList<DBox>();

            for (ValueEnumeration e = shape[i].valueEnumeration(); e.hasMoreElements(); ) {
                int j = e.nextElement();

                int[] offset = new int[dim];
                int[] size = new int[dim];

                for (int k = 0; k < dim; k++) {
                    offset[k] = rect_offset[(j - 1) * dim + k];
                    size[k] = rect_size[(j - 1) * dim + k];
                }
                shape_i.add(new DBox(offset, size));

            }
            shapes.add(new Shape((i + 1), shape_i));
        }

        // for (int i = 0; i < shapes.size(); i++)
        // 	System.out.println("*** " + shapes.get(i));

        ArrayList<GeostObject> objects = new ArrayList<GeostObject>();

        for (int i = 0; i < kind.length; i++) {

            IntVar[] coords = new IntVar[dim];

            for (int k = 0; k < dim; k++)
                coords[k] = x[i * dim + k];

            // System.out.println("coords = " + java.util.Arrays.asList(coords));

            IntVar start = new IntVar(store, "start[" + i + "]", 0, 0);
            IntVar duration = new IntVar(store, "duration[" + i + "]", 1, 1);
            IntVar end = new IntVar(store, "end[" + i + "]", 1, 1);
            GeostObject obj = new GeostObject(i, coords, kind[i], start, duration, end);
            objects.add(obj);
        }

        // System.out.println("===========");
        // for (int i = 0; i < objects.size(); i++)
        // 	System.out.println(objects.get(i));
        // System.out.println("===========");

        ArrayList<ExternalConstraint> constraints = new ArrayList<ExternalConstraint>();
        int[] dimensions = new int[dim + 1];
        for (int i = 0; i < dim + 1; i++)
            dimensions[i] = i;

        NonOverlapping constraint1 = new NonOverlapping(objects, dimensions);
        constraints.add(constraint1);

        { // part for geost_bb
            int[] lb = support.getIntArray((SimpleNode) node.jjtGetChild(6));
            int[] ub = support.getIntArray((SimpleNode) node.jjtGetChild(7));

            // System.out.print("[");
            // for (int i = 0; i < lb.length; i++)
            // 	System.out.print(" " + lb[i]);
            // System.out.print("]\n[");
            // for (int i = 0; i < ub.length; i++)
            // 	System.out.print(" " + ub[i]);
            // System.out.println("]");

            InArea constraint2 = new InArea(new DBox(lb, ub), null);
            constraints.add(constraint2);
        }

        support.pose(new Geost(objects, constraints, shapes));
    }

    boolean allVarOne(IntVar[] w) {
        for (int i = 0; i < w.length; i++)
            if (w[i].min() != 1)
                return false;
        return true;
    }

    boolean allVarGround(IntVar[] w) {
        for (int i = 0; i < w.length; i++)
            if (!w[i].singleton())
                return false;
        return true;
    }

    int[] uniqueIndex(IntVar[] vs) {

        ArrayList<Integer> il = new ArrayList<Integer>();
        HashSet<IntVar> varSet = new HashSet<IntVar>();
        for (int i = 0; i < vs.length; i++) {
            boolean r = varSet.add(vs[i]);
            if (r)
                il.add(i);
        }
        int[] x = new int[il.size()];
        for (int i = 0; i < x.length; i++)
            x[i] = il.get(i);

        return x;
    }
}
