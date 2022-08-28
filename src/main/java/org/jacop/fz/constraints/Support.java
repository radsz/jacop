/*
 * Support.java
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

import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.XeqY;
import org.jacop.core.*;
import org.jacop.floats.core.FloatVar;
import org.jacop.fz.*;
import org.jacop.satwrapper.SatTranslation;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/*
 * Basic support for generation of constraints in flatzinc
 *
 * @author Krzysztof Kuchcinski
 */
public class Support implements ParserTreeConstants {

    Store store;
    Tables dictionary;

    // ============ SAT solver interface ==============
    SatTranslation sat;

    public Options options;

    // =========== Annotations ===========
    public boolean boundsConsistency = true;
    public boolean domainConsistency = false;
    public int constraintPriority = -1;
    // defines_var-- not used yet
    public IntVar definedVar = null;

    // comparison operators
    final static int eq = 0, ne = 1, lt = 2, gt = 3, le = 4, ge = 5;

    boolean intPresent = true;
    boolean floatPresent = true;

    ArrayList<IntVar[]> parameterListForAlldistincts = new ArrayList<IntVar[]>();
    ArrayList<Constraint> delayedConstraints = new ArrayList<Constraint>();

    ReificationConstraints reif = new ReificationConstraints(this);
    ImplicationConstraints imply = new ImplicationConstraints(this);

    public Support(Store store, Tables d, SatTranslation sat) {
        this.store = store;
        this.dictionary = d;
        this.sat = sat;
    }

    public int getInt(ASTScalarFlatExpr node) {
        intPresent = true;

        if (node.getType() == 0) //int
            return node.getInt();
        if (node.getType() == 1) //bool
            return node.getInt();
        else if (node.getType() == 2) // ident
            return dictionary.getInt(node.getIdent());
        else if (node.getType() == 3) { // array access
            int[] intTable = dictionary.getIntArray(node.getIdent());
            if (intTable == null) {
                intPresent = false;
                return Integer.MIN_VALUE;
            } else
                return intTable[node.getInt()];
        } else {
            throw new IllegalArgumentException("getInt: Wrong parameter " + node);
        }
    }

    int getScalarFlatExpr(SimpleNode node, int i) {
        SimpleNode child = (SimpleNode) node.jjtGetChild(i);
        if (child.getId() == JJTSCALARFLATEXPR) {
            switch (((ASTScalarFlatExpr) child).getType()) {
                case 0: // int
                    return ((ASTScalarFlatExpr) child).getInt();
                case 1: // bool
                    return ((ASTScalarFlatExpr) child).getInt();
                case 2: // ident
                    return dictionary.getInt(((ASTScalarFlatExpr) child).getIdent());
                case 3: // array acces
                    return dictionary.getIntArray(((ASTScalarFlatExpr) child).getIdent())[((ASTScalarFlatExpr) child).getInt()];
                default: // string & float;
                    throw new IllegalArgumentException("Not supported scalar in parameter; compilation aborted.");
            }
        } else {
            throw new IllegalArgumentException("Not supported parameter assignment; compilation aborted.");
        }
    }

    int[] getIntArray(SimpleNode node) {
        if (node.getId() == JJTARRAYLITERAL) {
            int count = node.jjtGetNumChildren();
            int[] aa = new int[count];
            for (int i = 0; i < count; i++) {
                ASTScalarFlatExpr child = (ASTScalarFlatExpr) node.jjtGetChild(i);
                int el = getInt(child);
                //              if (el == Integer.MIN_VALUE)
                if (!intPresent)
                    return null;
                else
                    aa[i] = el;
            }
            return aa;
        } else if (node.getId() == JJTSCALARFLATEXPR) {
            if (((ASTScalarFlatExpr) node).getType() == 2) // ident
                return dictionary.getIntArray(((ASTScalarFlatExpr) node).getIdent());
            else {
                throw new IllegalArgumentException("Wrong type of int array; compilation aborted.");
            }
        } else {
            throw new IllegalArgumentException("Wrong type of int array; compilation aborted.");
        }
    }

    public IntVar getVariable(ASTScalarFlatExpr node) {
        if (node.getType() == 0) { // int
            int val = node.getInt();
            return dictionary.getConstant(val);
        }
        if (node.getType() == 1) { // bool
            int val = node.getInt();
            return dictionary.getConstant(val);
        } else if (node.getType() == 2) { // ident
            IntVar int_boolVar = dictionary.getVariable(node.getIdent());
            if (int_boolVar == null) {
                int bInt = dictionary.getInt(node.getIdent());
                return dictionary.getConstant(bInt); // new IntVar(store, bInt, bInt);
            }
            return int_boolVar;
        } else if (node.getType() == 3) { // array access
            if (node.getInt() >= dictionary.getVariableArray(node.getIdent()).length || node.getInt() < 0) {
                throw new IllegalArgumentException("Index out of bound for " + node.getIdent() + "[" + (node.getInt() + 1) + "]");
            } else {
                return dictionary.getVariableArray(node.getIdent())[node.getInt()];
            }
        } else {
            throw new IllegalArgumentException("Wrong parameter " + node);
        }
    }

    FloatVar getFloatVariable(ASTScalarFlatExpr node) {

        if (node.getType() == 5) { // float
            double val = node.getFloat();
            // if (val == 0) return zero;
            // else if (val == 1) return one;
            // else
            return new FloatVar(store, val, val);
        } else if (node.getType() == 2) { // ident
            FloatVar float_Var = dictionary.getFloatVariable(node.getIdent());
            if (float_Var == null) {
                double bFloat = dictionary.getFloat(node.getIdent());
                return new FloatVar(store, bFloat, bFloat);
            }
            return float_Var;
        } else if (node.getType() == 3) { // array access
            if (node.getInt() >= dictionary.getVariableFloatArray(node.getIdent()).length || node.getFloat() < 0) {
                throw new IllegalArgumentException("Index out of bound for " + node.getIdent() + "[" + (node.getInt() + 1) + "]");
            } else
                return dictionary.getVariableFloatArray(node.getIdent())[node.getInt()];
        } else {
            throw new IllegalArgumentException("getFloatVariable: Wrong parameter " + node);
        }
    }

    SetVar getSetVariable(SimpleNode node, int index) {

        SimpleNode child = (SimpleNode) node.jjtGetChild(index);
        if (child.getId() == JJTSETLITERAL) {
            int count = child.jjtGetNumChildren();
            if (count == 0)
                return new SetVar(store, new BoundSetDomain(new IntervalDomain(), new IntervalDomain()));
            else {
                IntDomain s2 = getSetLiteral(node, index);
                return new SetVar(store, new BoundSetDomain(s2, s2));
            }
        } else if (child.getId() == JJTSCALARFLATEXPR) {
            if (((ASTScalarFlatExpr) child).getType() == 2) { // ident
                SetVar v = dictionary.getSetVariable(((ASTScalarFlatExpr) child).getIdent());
                if (v != null)
                    return v;  // Variable ident
                else { // Set ident
                    IntDomain s = dictionary.getSet(((ASTScalarFlatExpr) child).getIdent());
                    return new SetVar(store, new BoundSetDomain(s, s));
                }
            } else if (((ASTScalarFlatExpr) child).getType() == 3) // array access
                return dictionary.getSetVariableArray(((ASTScalarFlatExpr) child).getIdent())[((ASTScalarFlatExpr) child).getInt()];
            else {
                throw new IllegalArgumentException("Wrong parameter in set " + child);
            }
        } else {
            throw new IllegalArgumentException("Wrong parameter in set " + child);
        }
    }

    double getFloat(ASTScalarFlatExpr node) {
        floatPresent = true;

        if (node.getType() == 5) //int
            return node.getFloat();
        else if (node.getType() == 2) // ident
            return dictionary.getFloat(node.getIdent());
        else if (node.getType() == 3) { // array access
            double[] floatTable = dictionary.getFloatArray(node.getIdent());
            if (floatTable == null) {
                floatPresent = false;
                return VariablesParameters.MIN_FLOAT;
            } else
                return floatTable[node.getInt()];
        } else {
            throw new IllegalArgumentException("getFloat: Wrong parameter " + node);
        }
    }

    double[] getFloatArray(SimpleNode node) {
        if (node.getId() == JJTARRAYLITERAL) {
            int count = node.jjtGetNumChildren();
            double[] aa = new double[count];
            for (int i = 0; i < count; i++) {
                ASTScalarFlatExpr child = (ASTScalarFlatExpr) node.jjtGetChild(i);
                double el = getFloat(child);
                if (!floatPresent)
                    return null;
                else
                    aa[i] = el;
            }
            return aa;
        } else if (node.getId() == JJTSCALARFLATEXPR) {
            if (((ASTScalarFlatExpr) node).getType() == 2) // ident
                return dictionary.getFloatArray(((ASTScalarFlatExpr) node).getIdent());
            else {
                throw new IllegalArgumentException("Wrong type of int array; compilation aborted.");
            }
        } else {
            throw new IllegalArgumentException("Wrong type of int array; compilation aborted.");
        }
    }


    IntVar[] getVarArray(SimpleNode node) {
        if (node.getId() == JJTARRAYLITERAL) {
            int count = node.jjtGetNumChildren();
            IntVar[] aa = new IntVar[count];
            for (int i = 0; i < count; i++) {
                ASTScalarFlatExpr child = (ASTScalarFlatExpr) node.jjtGetChild(i);
                IntVar el = getVariable(child);
                aa[i] = el;
            }
            return aa;
        } else if (node.getId() == JJTSCALARFLATEXPR) {
            if (((ASTScalarFlatExpr) node).getType() == 2) { // ident
                // array of var
                IntVar[] v = dictionary.getVariableArray(((ASTScalarFlatExpr) node).getIdent());
                if (v != null)
                    return v;
                else { // array of int
                    int[] ia = dictionary.getIntArray(((ASTScalarFlatExpr) node).getIdent());
                    if (ia != null) {
                        IntVar[] aa = new IntVar[ia.length];
                        for (int i = 0; i < ia.length; i++)
                            aa[i] = dictionary.getConstant(ia[i]); // new IntVar(store, ia[i], ia[i]);
                        return aa;
                    } else {
                        throw new IllegalArgumentException(
                            "Cannot find array " + ((ASTScalarFlatExpr) node).getIdent() + "; compilation aborted.");
                    }
                }
            } else {
                throw new IllegalArgumentException("Wrong type of Variable array; compilation aborted.");
            }
        } else {
            throw new IllegalArgumentException("Wrong type of Variable array; compilation aborted.");
        }
    }

    FloatVar[] getFloatVarArray(SimpleNode node) {
        if (node.getId() == JJTARRAYLITERAL) {
            int count = node.jjtGetNumChildren();
            FloatVar[] aa = new FloatVar[count];
            for (int i = 0; i < count; i++) {
                ASTScalarFlatExpr child = (ASTScalarFlatExpr) node.jjtGetChild(i);
                FloatVar el = getFloatVariable(child);
                aa[i] = el;
            }
            return aa;
        } else if (node.getId() == JJTSCALARFLATEXPR) {
            if (((ASTScalarFlatExpr) node).getType() == 2) { // ident
                // array of var
                FloatVar[] v = dictionary.getVariableFloatArray(((ASTScalarFlatExpr) node).getIdent());
                return v;
            } else {
                throw new IllegalArgumentException("Wrong type of Variable array; compilation aborted.");
            }
        } else {
            throw new IllegalArgumentException("Wrong type of Variable array; compilation aborted.");
        }
    }

    IntDomain[] getSetArray(SimpleNode node) {
        IntDomain[] s = null;
        int arrayIndex = 0;

        if (node.getId() == JJTARRAYLITERAL) {
            int count = node.jjtGetNumChildren();
            s = new IntDomain[count];
            for (int i = 0; i < count; i++) {
                s[arrayIndex++] = getSetLiteral(node, i);
            }
        } else if (node.getId() == JJTSCALARFLATEXPR) {
            if (((ASTScalarFlatExpr) node).getType() == 2) { // ident
                s = dictionary.getSetArray(((ASTScalarFlatExpr) node).getIdent());
                if (s == null) { // there is still a chance that the var_array has constant sets ;)
                    SetVar[] sVar = dictionary.getSetVariableArray(((ASTScalarFlatExpr) node).getIdent());
                    int numberSingleton = 0;
                    for (int i = 0; i < sVar.length; i++)
                        if (sVar[i].singleton())
                            numberSingleton++;
                    if (sVar.length == numberSingleton) {
                        s = new IntDomain[sVar.length];
                        for (int i = 0; i < sVar.length; i++)
                            s[i] = sVar[i].dom().glb();
                        //                          System.out.println(((SetDomain)sVar[i].dom()).glb());
                    }
                }
            } else {
                throw new IllegalArgumentException("Wrong set array.");
            }
        }
        return s;
    }

    SetVar[] getSetVarArray(SimpleNode node) {
        SetVar[] s = null;
        // int arrayIndex = 0;

        if (node.getId() == JJTARRAYLITERAL) {
            int count = node.jjtGetNumChildren();
            s = new SetVar[count];
            for (int i = 0; i < count; i++) {
                SetVar el = getSetVariable(node, i);
                s[i] = el;
            }
            return s;
        } else if (node.getId() == JJTSCALARFLATEXPR) {
            if (((ASTScalarFlatExpr) node).getType() == 2) { // ident
                s = dictionary.getSetVariableArray(((ASTScalarFlatExpr) node).getIdent());
                if (s != null)
                    return s;
                else
                    throw new IllegalArgumentException("Wrong set variable array; compilation aborted.");
            } else
                throw new IllegalArgumentException("Wrong set variable array; compilation aborted.");
        } else
            throw new IllegalArgumentException("Wrong set variable array; compilation aborted.");
    }

    IntDomain getSetLiteral(SimpleNode node, int index) {
        // node.dump("Support.getSetLiteral ");
        SimpleNode child = (SimpleNode) node.jjtGetChild(index);
        if (child.getId() == JJTSETLITERAL) {
            switch (((ASTSetLiteral) child).getType()) {
                case 0: // interval
                    SimpleNode grand_child_1 = (SimpleNode) child.jjtGetChild(0);
                    SimpleNode grand_child_2 = (SimpleNode) child.jjtGetChild(1);
                    if (grand_child_1.getId() == JJTINTFLATEXPR && grand_child_2.getId() == JJTINTFLATEXPR) {
                        int i1 = ((ASTIntFlatExpr) grand_child_1).getInt();
                        int i2 = ((ASTIntFlatExpr) grand_child_2).getInt();
                        if (i1 > i2)
                            return new IntervalDomain();
                        else
                            return new IntervalDomain(i1, i2);
                    }
                    break;
                case 1: // list
                    IntDomain s = new IntervalDomain();
                    int el = -1111;
                    int count = child.jjtGetNumChildren();
                    for (int i = 0; i < count; i++) {
                        el = getScalarFlatExpr(child, i);
                        s.unionAdapt(el);
                    }
                    return s;
                case 2: // range
                    IntDomain d = new IntervalDomain();
                    int n = child.jjtGetNumChildren();
                    for (int i = 0; i < n; i++) {

                        SimpleNode setElement = (SimpleNode) child.jjtGetChild(i);
                        if (setElement.getId() == JJTSETELEMENT) {
                            SimpleNode e1 = (SimpleNode) setElement.jjtGetChild(0);
                            if (e1.getId() == JJTSCALARFLATEXPR) {
                                d.unionAdapt(((ASTScalarFlatExpr) e1).getInt());
                            } else if (e1.getId() == JJTINTFLATEXPR) {
                                SimpleNode e2 = (SimpleNode) setElement.jjtGetChild(1);
                                d.unionAdapt(new Interval(((ASTIntFlatExpr) e1).getInt(), ((ASTIntFlatExpr) e2).getInt()));
                            }
                        }
                    }
                    return d;
                default:
                    throw new IllegalArgumentException("Set type not supported; compilation aborted.");
            }
        } else if (child.getId() == JJTSCALARFLATEXPR) {
            switch (((ASTScalarFlatExpr) child).getType()) {
                case 0: // int
                case 1: // bool
                    throw new IllegalArgumentException("Set initialization fault; compilation aborted.");
                case 2: // ident
                    return dictionary.getSet(((ASTScalarFlatExpr) child).getIdent());
                case 3: // array access
                    return dictionary.getSetArray(((ASTScalarFlatExpr) child).getIdent())[((ASTScalarFlatExpr) child).getInt()];
                case 4: // string
                case 5: // float
                    throw new IllegalArgumentException("Set initialization fault; compilation aborted.");
                default:
                    throw new IllegalArgumentException("Set initialization fault; compilation aborted.");
            }
        }
        return new IntervalDomain();
    }

    IntVar[] unique(IntVar[] vs) {

        LinkedHashSet<IntVar> varSet = new LinkedHashSet<IntVar>();
        for (IntVar v : vs)
            varSet.add(v);

        int l = varSet.size();
        IntVar[] rs = new IntVar[l];

        int i = 0;
        for (IntVar v : varSet) {
            rs[i++] = v;
        }

        return rs;
    }

    public void parseAnnotations(SimpleNode constraintWithAnnotations) {

        for (int i = 1; i < constraintWithAnnotations.jjtGetNumChildren(); i++) {
            ASTAnnotation ann = (ASTAnnotation) constraintWithAnnotations.jjtGetChild(i);

            // ann.dump("");
            // System.out.println ("ann["+i+"] = "+ ann.getAnnId());
            constraintPriority = -1;

            if (ann.getAnnId().equals("$expr")) {
                ASTScalarFlatExpr n = (ASTScalarFlatExpr)ann.jjtGetChild(0).jjtGetChild(0);
                if (n.getIdent().equals("bounds") || n.getIdent().equals("boundsZ")) {
                    boundsConsistency = true;
                    domainConsistency = false;
                } else if (n.getIdent().equals("domain")) {
                    boundsConsistency = false;
                    domainConsistency = true;
                }
            } else if (ann.getAnnId().equals("defines_var")) {  // no used in JaCoP yet
                SimpleNode child = (SimpleNode) ann.jjtGetChild(0);
                ASTAnnExpr expr = (ASTAnnExpr) child.jjtGetChild(0);
                Var v = getAnnVar(expr);

                definedVar = (IntVar) v;
            } else if (ann.getAnnId().equals("priority")) {
                SimpleNode child = (SimpleNode) ann.jjtGetChild(0);
                ASTAnnExpr expr = (ASTAnnExpr) child.jjtGetChild(0);
                int val = getAnnInt(expr);

                constraintPriority = val;
            }

        }
        // System.out.println("defines " + definedVar);
    }

    Var getAnnVar(ASTAnnExpr node) {

        ASTScalarFlatExpr e = (ASTScalarFlatExpr) node.jjtGetChild(0);
        if (e != null)
            return dictionary.getVariable(e.getIdent());
        else {
            throw new IllegalArgumentException("Wrong variable identified in \"defines_var\" annotation" + node);
        }
    }

    int getAnnInt(ASTAnnExpr node) {

        ASTScalarFlatExpr e = (ASTScalarFlatExpr) node.jjtGetChild(0);
        if (e != null) {
            return getInt(e);
        } else {
            throw new IllegalArgumentException("Wrong definition od \"priority\" annotation" + node);
        }
    }

    public void poseDelayedConstraints() {
        // generate channeling constraints for aliases
        // variables that are output variables
        aliasConstraints();

        for (Constraint c : delayedConstraints) {
            store.impose(c);
            if (options.debug()) {
                String s = "% " + c.toString();
                System.out.println(s.replaceAll("\n", "\n% "));
            }
        }
        poseAlldistinctConstraints();

        // generate channeling constraints instead of reified constraints
        reif.pose();
        // generate channeling constraints instead of implied constraints
        imply.pose();
    }

    void poseAlldistinctConstraints() {
        for (IntVar[] v : parameterListForAlldistincts) {
            Alldistinct ad = new Alldistinct(v);
            store.impose(ad);
            if (options.debug()) {
                String s = "% " + ad.toString();
                System.out.println(s.replaceAll("\n", "\n% "));
            }
        }
    }

    void aliasConstraints() {

        Set<Map.Entry<IntVar, IntVar>> entries = dictionary.aliasTable.entrySet();

        for (Map.Entry<IntVar, IntVar> e : entries) {
            IntVar v = e.getKey();
            IntVar b = e.getValue();

            // give values to output vars
            if (dictionary.isOutput(v))
                pose(new XeqY(v, b));
        }
    }

    void poseDC(DecomposedConstraint c) throws FailException {

        store.imposeDecompositionWithConsistency(c);
        if (options.debug()) {
            String s = "% " + c.toString();
            System.out.println(s.replaceAll("\n", "\n% "));
        }
    }

    void pose(Constraint c) throws FailException {

        if (constraintPriority >= 0 && constraintPriority <= 4)
            store.imposeWithConsistency(c, constraintPriority);
        else
            store.imposeWithConsistency(c);

        if (options.debug()) {
            String s = "% " + c.toString();
            System.out.println(s.replaceAll("\n", "\n% "));
        }
    }

    public void addReified(IntVar x, int v, IntVar b) {
        reif.add(x, v, b);
    }

    public void poseReified(Support s) {
        reif.pose();
    }

    public void addImplied(IntVar x, int v, IntVar b) {
        imply.add(x, v, b);
    }

    public void poseImplied(Support s) {
        imply.pose();
    }

    // =========== Specialized constraints ===================

    Constraint fzXeqCReified(IntVar x, int c, IntVar b) {

        return new Constraint(new IntVar[] {x, b}) {

            @Override public void consistency(final Store store) {

                if (x.singleton(c)) {
                    b.domain.inValue(store.level, b, 1);
                } else if (!x.domain.contains(c)) {
                    b.domain.inValue(store.level, b, 0);
                    removeConstraint();
                } else if (b.max() == 0) { // x==c must be false
                    x.domain.inComplement(store.level, x, c);
                    removeConstraint();
                } else if (b.min() == 1) // x==c must be true
                    x.domain.inValue(store.level, x, c);
            }

            @Override public int getDefaultConsistencyPruningEvent() {
                return IntDomain.ANY;
            }

            @Override public String toString() {
                return "fz : XeqC_Reified(" + x + ", " + c + ", " + b + " )";
            }
        };
    }

    Constraint fzXeqCImplied(IntVar x, int c, IntVar b) {

        return new Constraint(new IntVar[] {x, b}) {

            @Override public void consistency(final Store store) {

                if (x.singleton(c)) {
                    removeConstraint();
                } else if (!x.domain.contains(c)) {
                    b.domain.inValue(store.level, b, 0);
                    removeConstraint();
                } else if (b.max() == 0) {
                    removeConstraint();
                } else if (b.min() == 1) { // x==c must be true
                    x.domain.inValue(store.level, x, c);
                }
            }

            @Override public int getDefaultConsistencyPruningEvent() {
                return IntDomain.ANY;
            }

            @Override public String toString() {
                return "fz : XeqC_Implied(" + b + ", " + x + ", " + c + " )";
            }
        };
    }

    Constraint fzXneqCReified(IntVar x, int c, IntVar b) {

        return new Constraint(new IntVar[] {x, b}) {

            @Override public void consistency(final Store store) {

                if (x.singleton(c)) {
                    b.domain.inValue(store.level, b, 0);
                } else if (!x.domain.contains(c)) {
                    b.domain.inValue(store.level, b, 1);
                    removeConstraint();
                } else if (b.max() == 0) { // x!=c must be false
                    x.domain.inValue(store.level, x, c);
                    removeConstraint();
                } else if (b.min() == 1) { // x!=c must be true
                    x.domain.inComplement(store.level, x, c);
                    removeConstraint();
                }
            }

            @Override public int getDefaultConsistencyPruningEvent() {
                return IntDomain.ANY;
            }

            @Override public String toString() {
                return "fz : XneqC_Reified(" + x + ", " + c + ", " + b + " )";
            }
        };
    }

    Constraint fzXneqCImplied(IntVar x, int c, IntVar b) {

        return new Constraint(new IntVar[] {x, b}) {

            @Override public void consistency(final Store store) {

                if (x.singleton(c)) {
                    b.domain.inValue(store.level, b, 0);
                } else if (!x.domain.contains(c)) {
                    removeConstraint();
                } else if (b.max() == 0) {
                    removeConstraint();
                } else if (b.min() == 1) { // x!=c must be true
                    x.domain.inComplement(store.level, x, c);
                }
            }

            @Override public int getDefaultConsistencyPruningEvent() {
                return IntDomain.ANY;
            }

            @Override public String toString() {
                return "fz : XneqC_Implied(" + b + ", " + x + ", " + c + " )";
            }
        };
    }
}
