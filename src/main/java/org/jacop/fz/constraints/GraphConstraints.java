/*
 * GraphConstraints.java
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

import org.jacop.constraints.*;
import org.jacop.core.*;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import java.lang.reflect.Constructor;
import java.util.Arrays;
import java.util.Set;

/*
 * Generation of graph constraints in flatzinc.
 *
 * @author Krzysztof Kuchcinski
 */
class GraphConstraints implements ParserTreeConstants {

    Store store;
    Support support;

    public GraphConstraints(Support support) {
        this.store = support.store;
        this.support = support;
    }

    void gen_jacop_graph_isomorphism(SimpleNode node) {

        IntDomain[] t = support.getSetArray((SimpleNode) node.jjtGetChild(0));
        IntDomain[] p = support.getSetArray((SimpleNode) node.jjtGetChild(1));
        int[] targetType = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        int[] patternType = support.getIntArray((SimpleNode) node.jjtGetChild(3));
        IntVar[] m = support.getVarArray((SimpleNode) node.jjtGetChild(4));
        int offset = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
        String cName = "GraphIsomorphism";

        // support.poseDC(new GraphIsomorphism(t, p, targetType, patternType, m, offset));

        try {
            Class<?> c = Class.forName("org.jacop.graph." + cName);
            Constructor<?> cons = c.getConstructor(IntDomain[].class, IntDomain[].class,
                                                   int[].class, int[].class, IntVar[].class, int.class);
            Object constraint = cons.newInstance(t, p, targetType, patternType, m, offset);
            support.poseDC((DecomposedConstraint)constraint);

        } catch (java.lang.ClassNotFoundException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.NoSuchMethodException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.InstantiationException e) {
            throw new RuntimeException("% Constraint "
                                       + cName + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.IllegalAccessException e) {
            throw new RuntimeException("% Constraint "
                                       + cName + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.reflect.InvocationTargetException e) {
            throw new RuntimeException("% Constraint "
                                       + cName + " is not available in this version; requires org.jacop.graph.");
        }
    }
    
    void gen_jacop_graph_match(SimpleNode node) {
        int[] t = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        int[] p = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int[] target_type = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        int[] pattern_type = support.getIntArray((SimpleNode) node.jjtGetChild(3));
        IntVar[] match = support.getVarArray((SimpleNode) node.jjtGetChild(4));
        int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
        String cName = "GraphMatch";

        /*
        GraphMatch c = new GraphMatch(store, t, p, target_type, pattern_type, index_min, match, true);
        support.pose(c);

        IntVar[] matchVars = c.variables();

        if (index_min == 0)
            for (int i = 0; i < match.length; i++) 
                support.pose(new XeqY(matchVars[i], match[i]));
        else
            for (int i = 0; i < match.length; i++)
                support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
        */

        try {
            IntVar[] matchVars = null;
            if (index_min == 0)
                for (int i = 0; i < match.length; i++) 
                    matchVars = match;
            else {
                matchVars = new IntVar[match.length];
                for (int i = 0; i < match.length; i++) {
                    matchVars[i] = new IntVar(store, "node_" + i, 0, pattern_type.length - 1);
                    support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
                }
            }

            Class<?> c = Class.forName("org.jacop.graph." + cName);
            Constructor<?> cons = c.getConstructor(Store.class, int[].class, int[].class,
                                                   int[].class, int[].class, int.class, IntVar[].class, boolean.class);
            Object constraint = cons.newInstance(store, t, p, target_type, pattern_type, index_min, matchVars, true);
            support.pose((Constraint)constraint);

        } catch (java.lang.ClassNotFoundException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.NoSuchMethodException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.InstantiationException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.IllegalAccessException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.reflect.InvocationTargetException e) {
            throw new RuntimeException("% Constraint " + cName + " is not available in this version; requires org.jacop.graph.");
        }
    }

    void gen_jacop_digraph_match(SimpleNode node) {
        int[] t = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        int[] p = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int[] target_type = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        int[] pattern_type = support.getIntArray((SimpleNode) node.jjtGetChild(3));
        IntVar[] match = support.getVarArray((SimpleNode) node.jjtGetChild(4));
        int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
        String cName = "GraphMatch";

        /*
        Graph target = buildDiGraph(t, target_type, index_min);
        Graph pattern = buildDiGraph(p, pattern_type, index_min);

        GraphMatch c = new GraphMatch(store, target, pattern);
        support.pose(c);
        IntVar[] matchVars = c.variables();

        if (index_min == 0)
            for (int i = 0; i < match.length; i++) 
                support.pose(new XeqY(matchVars[i], match[i]));
        else
            for (int i = 0; i < match.length; i++)
                support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
        */

        try {
            IntVar[] matchVars = null;
            if (index_min == 0)
                for (int i = 0; i < match.length; i++) 
                    matchVars = match;
            else {
                matchVars = new IntVar[match.length];
                for (int i = 0; i < match.length; i++) {
                    matchVars[i] = new IntVar(store, "node_" + i, 0, pattern_type.length - 1);
                    support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
                }
            }

            Class<?> c = Class.forName("org.jacop.graph." + cName);
            Constructor<?> cons = c.getConstructor(Store.class, int[].class, int[].class,
                                                   int[].class, int[].class, int.class, IntVar[].class, boolean.class);
            Object constraint = cons.newInstance(store, t, p, target_type, pattern_type, index_min, matchVars, false);
            support.pose((Constraint)constraint);

        } catch (java.lang.ClassNotFoundException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.NoSuchMethodException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.InstantiationException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.IllegalAccessException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.reflect.InvocationTargetException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        }
    }

    void gen_jacop_sub_graph_match(SimpleNode node) {
        int[] t = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        int[] p = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int[] target_type = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        int[] pattern_type = support.getIntArray((SimpleNode) node.jjtGetChild(3));
        IntVar[] match = support.getVarArray((SimpleNode) node.jjtGetChild(4));
        int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
        String cName = "SubGraphMatch";

        /*
        Graph target = buildGraph(t, target_type, index_min);
        Graph pattern = buildGraph(p, pattern_type, index_min);

        SubGraphMatch c = new SubGraphMatch(store, target, pattern);
        support.pose(c);
        IntVar[] matchVars = c.variables();

        if (matchVars.length != match.length)
            throw new IllegalArgumentException("%% ERROR: sub_graph_match must have pattern size the same as pattern graph");
            
        if (index_min == 0)
            for (int i = 0; i < match.length; i++) 
                support.pose(new XeqY(matchVars[i], match[i]));
        else
            for (int i = 0; i < match.length; i++)
                support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
        */

        try {
            IntVar[] matchVars = null;
            if (index_min == 0)
                for (int i = 0; i < match.length; i++) 
                    matchVars = match;
            else {
                matchVars = new IntVar[match.length];
                for (int i = 0; i < match.length; i++) {
                    matchVars[i] = new IntVar(store, "node_" + i, 0, target_type.length - 1);
                    support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
                }
            }

            Class<?> c = Class.forName("org.jacop.graph." + cName);
            Constructor<?> cons = c.getConstructor(Store.class, int[].class, int[].class,
                                                   int[].class, int[].class, int.class, IntVar[].class, boolean.class);
            Object constraint = cons.newInstance(store, t, p, target_type, pattern_type, index_min, matchVars, true);
            support.pose((Constraint)constraint);

        } catch (java.lang.ClassNotFoundException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.NoSuchMethodException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.InstantiationException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.IllegalAccessException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.reflect.InvocationTargetException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        }
    }

    void gen_jacop_sub_digraph_match(SimpleNode node) {
        int[] t = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        int[] p = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int[] target_type = support.getIntArray((SimpleNode) node.jjtGetChild(2));
        int[] pattern_type = support.getIntArray((SimpleNode) node.jjtGetChild(3));
        IntVar[] match = support.getVarArray((SimpleNode) node.jjtGetChild(4));
        int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
        String cName = "SubGraphMatch";

        /*
        Graph target = buildDiGraph(t, target_type, index_min);
        Graph pattern = buildDiGraph(p, pattern_type, index_min);

        // GraphMatchDecomposed c = new GraphMatchDecomposed(store, target, pattern);
        // support.poseDC(c);
        SubGraphMatch c = new SubGraphMatch(store, target, pattern);
        support.pose(c);
        IntVar[] matchVars = c.variables();

        if (matchVars.length != match.length)
            throw new IllegalArgumentException("%% ERROR: sub_digraph_match must have pattern size the same as pattern graph");

        if (index_min == 0)
            for (int i = 0; i < match.length; i++) 
                support.pose(new XeqY(matchVars[i], match[i]));
        else
            for (int i = 0; i < match.length; i++)
                support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
        */
        
        try {
            IntVar[] matchVars = null;
            if (index_min == 0)
                for (int i = 0; i < match.length; i++) 
                    matchVars = match;
            else {
                matchVars = new IntVar[match.length];
                for (int i = 0; i < match.length; i++) {
                    matchVars[i] = new IntVar(store, "node_" + i, 0, target_type.length - 1);
                    support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
                }
            }

            Class<?> c = Class.forName("org.jacop.graph." + cName);
            Constructor<?> cons = c.getConstructor(Store.class, int[].class, int[].class,
                                                   int[].class, int[].class, int.class, IntVar[].class, boolean.class);
            Object constraint = cons.newInstance(store, t, p, target_type, pattern_type, index_min, matchVars, false);
            support.pose((Constraint)constraint);

        } catch (java.lang.ClassNotFoundException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.NoSuchMethodException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.InstantiationException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.IllegalAccessException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.reflect.InvocationTargetException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        }
    }

    void gen_jacop_clique(SimpleNode node) {
        int[] g = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] c = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        String cName = "Clique";

        int[] type = new int[c.length];
        Arrays.fill(type, 1);

        IntVar cost = new IntVar(store, 0, IntDomain.MaxInt);

        // Graph graph = buildGraph(g, type, index_min);

        // // CliqueDecomposed ctr = new CliqueDecomposed(store, graph, cost);
        // // support.poseDC(ctr);
        // Clique ctr = new Clique(store, graph, cost);
        // support.pose(ctr);
        // IntVar[] vars = ctr.variables();

        // if (vars.length != c.length)
        //     throw new IllegalArgumentException("%% ERROR: sub_digraph_match must have pattern size the same as pattern graph");

        // for (int i = 0; i < c.length; i++) 
        //     support.pose(new XeqY(vars[i], c[i]));

        try {
            Class<?> cls = Class.forName("org.jacop.graph." + cName);
            Constructor<?> cons = cls.getConstructor(Store.class, int[].class, int[].class,
                                                     int.class, IntVar[].class, IntVar.class);
            Object constraint = cons.newInstance(store, g, type, index_min, c, cost);
            support.pose((Constraint)constraint);

        } catch (java.lang.ClassNotFoundException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.NoSuchMethodException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.InstantiationException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.IllegalAccessException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        } catch (java.lang.reflect.InvocationTargetException e) {
            throw new RuntimeException("% Constraint " + cName
                                       + " is not available in this version; requires org.jacop.graph.");
        }
    }
}
