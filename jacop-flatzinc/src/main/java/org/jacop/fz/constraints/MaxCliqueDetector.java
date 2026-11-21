/*
 * MaxCliqueDetector.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */
package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.MaxCliqueBound;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ASTSolveExpr;
import org.jacop.fz.ASTSolveKind;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds a maximized objective that is the sum of 0/1 variables of which some pairs cannot both
 * be 1, {@code z = x[1] + ... + x[n]} with the conflicts {@code x[i] + x[j] <= 1} ({@code
 * int_lin_le([1, 1], [x[i], x[j]], 1)}, {@code bool_clause([], [x[i], x[j]])} or {@code
 * array_bool_and([x[i], x[j]], false)}), and posts {@link MaxCliqueBound} on it as a redundant
 * constraint: maximum clique (of the graph of the pairs not in conflict) and maximum independent
 * set models. The linear objective and the conflicts are still posted; the constraint adds the
 * coloring bound of maximum clique algorithms, which a linear sum over pairwise constraints does
 * not see.
 *
 * <p>Setting the system property {@code org.jacop.fz.maxClique} to false turns the detection off. A
 * model that is maximum clique and nothing else is solved without LCG unless {@code --lcg} is given
 * ({@link #pure}); the system property {@code org.jacop.fz.maxClique.lcg} set to true keeps LCG on
 * by default for it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class MaxCliqueDetector implements ParserTreeConstants {

  // the fewest vertices worth the bound
  private static final int MIN_VERTICES = 10;

  // the most vertices: the graph is kept as bit sets, n * n / 8 bytes
  private static final int MAX_VERTICES = 5_000;

  private final Support support;

  private final Map<IntVar, IntVar> bool2int = new IdentityHashMap<>();

  private final List<IntVar[]> pairs = new ArrayList<>();

  // the constraints of the pairs
  private final Set<SimpleNode> pairNodes = new HashSet<>();

  private final List<ASTConstElem> linears = new ArrayList<>();

  private IntVar objective;

  // the constraints that are neither conflicts, nor bool2int, nor a sum
  private int others;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public MaxCliqueDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.maxClique is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.maxClique"));
  }

  /**
   * It tells if a model of maximum clique only keeps LCG on by default.
   *
   * @return true if the system property org.jacop.fz.maxClique.lcg is true.
   */
  public static boolean keepsLcg() {
    return Boolean.getBoolean("org.jacop.fz.maxClique.lcg");
  }

  /**
   * It scans the model and posts the bound on a maximized sum of 0/1 variables in conflict.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    IntVar[] vertices = scan(astTree);
    if (vertices != null) {
      MaxCliqueBound bound = post(vertices);
      if (bound != null
          && others == 0
          && linears.size() == 1
          && pairs.size() >= vertices.length
          && pairsOnVertices(vertices)) {
        // maximum clique and nothing else: its default search branches as clique algorithms do
        support.dictionary.maxClique = bound;
      }
    }
  }

  /**
   * It tells if a model of maximum clique only, without a search annotation, is searched by the
   * branching of maximum clique algorithms ({@link org.jacop.search.MaxCliqueSelect}).
   *
   * @return false if the system property org.jacop.fz.maxClique.search is false.
   */
  public static boolean searches() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.maxClique.search"));
  }

  /**
   * It tells if the model is a maximum clique model and nothing else: the maximized sum, its
   * conflicts and the bool2int of its variables. Such a model is solved best by branch and bound
   * with the coloring bound and without learning, as maximum clique algorithms do; the reasons of
   * the bound, which cite the zeros of the vertices, make the clauses that LCG learns weak.
   *
   * @param astTree the root of the parsed model.
   * @return true for a model of maximum clique only
   */
  public boolean pure(SimpleNode astTree) {
    IntVar[] vertices = scan(astTree);
    return vertices != null
        && others == 0
        && linears.size() == 1
        && pairs.size() >= vertices.length
        && pairsOnVertices(vertices);
  }

  // whether every conflict is between two vertices of the sum, so that the bound holds them all: a
  // conflict over another variable, such as one declared equal to a vertex, must stay posted
  private boolean pairsOnVertices(IntVar[] vertices) {
    Map<IntVar, Integer> index = vertexIndex(vertices);
    for (IntVar[] p : pairs) {
      Integer i = vertexOf(index, p[0]);
      Integer j = vertexOf(index, p[1]);
      if (i == null || j == null || i.equals(j)) {
        return false;
      }
    }
    return true;
  }

  private Map<IntVar, Integer> vertexIndex(IntVar[] vertices) {
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    for (int i = 0; i < vertices.length; i++) {
      index.put(vertices[i], i);
      index.putIfAbsent(source(vertices[i]), i);
    }
    return index;
  }

  private Integer vertexOf(Map<IntVar, Integer> index, IntVar v) {
    Integer i = index.get(v);
    return i != null ? i : index.get(source(v));
  }

  /**
   * The pairwise conflicts of a model of maximum clique and nothing else, which the bound enforces
   * by itself, so they need not be posted: their propagators cost more than half of the time of
   * branch and bound on brock400 and make the sequence detector post AmongSeq over chains of
   * consecutive pairs.
   *
   * @param astTree the root of the parsed model.
   * @return the constraints of the conflicts, empty unless the model is pure maximum clique and the
   *     system property org.jacop.fz.maxClique.pairs is not true
   */
  public Set<SimpleNode> replacedPairs(SimpleNode astTree) {
    if (Boolean.getBoolean("org.jacop.fz.maxClique.pairs") || !pure(astTree)) {
      return Set.of();
    }
    return pairNodes;
  }

  // the vertices of the maximized sum with conflicts, or null
  private IntVar[] scan(SimpleNode astTree) {
    objective(astTree);
    if (objective == null) {
      return null;
    }
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item);
          }
        }
      }
    }
    if (pairs.isEmpty()) {
      return null;
    }
    for (ASTConstElem node : linears) {
      IntVar[] vertices = objectiveSum(node);
      if (vertices != null) {
        return vertices;
      }
    }
    return null;
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar variable(ASTConstElem node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private static boolean zeroOne(IntVar v) {
    return v.min() >= 0 && v.max() <= 1;
  }

  // the variable a 0/1 variable stands for: the Boolean of its bool2int
  private IntVar source(IntVar v) {
    IntVar b = bool2int.get(v);
    return b == null ? v : b;
  }

  private void pair(ASTConstElem node, IntVar a, IntVar b) {
    if (a != b && zeroOne(a) && zeroOne(b)) {
      pairs.add(new IntVar[] {a, b});
      pairNodes.add(node);
    } else {
      others++;
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "bool2int" -> {
        IntVar b = variable(node, 0);
        IntVar i = variable(node, 1);
        if (b != i) {
          bool2int.put(i, b);
        }
      }
      case "int_lin_le", "bool_lin_le" -> {
        int[] a = support.getIntArray(child(node, 0));
        IntVar[] x = support.getVarArray(child(node, 1));
        int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (a != null && a.length == 2 && x.length == 2 && a[0] == 1 && a[1] == 1 && c == 1) {
          pair(node, x[0], x[1]);
        } else {
          others++;
        }
      }
      case "bool_clause" -> {
        IntVar[] pos = support.getVarArray(child(node, 0));
        IntVar[] neg = support.getVarArray(child(node, 1));
        if (pos.length == 0 && neg.length == 2) {
          pair(node, neg[0], neg[1]);
        } else {
          others++;
        }
      }
      case "array_bool_and" -> {
        IntVar[] x = support.getVarArray(child(node, 0));
        IntVar r = variable(node, 1);
        if (x.length == 2 && r.singleton(0)) {
          pair(node, x[0], x[1]);
        } else {
          others++;
        }
      }
      case "int_lin_eq" -> linears.add(node);
      default -> others++;
    }
  }

  // the variable of maximize, null otherwise
  private void objective(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() != JJTMODELEND || node.jjtGetNumChildren() == 0) {
        continue;
      }
      SimpleNode item = child(node, 0);
      SimpleNode last = child(item, item.jjtGetNumChildren() - 1);
      if (last instanceof ASTSolveKind kind
          && "maximize".equals(kind.getKind())
          && last.jjtGetNumChildren() > 0
          && child(kind, 0) instanceof ASTSolveExpr expr) {
        if (expr.getType() == 0) {
          objective = support.dictionary.getVariable(expr.getIdent());
        } else if (expr.getType() == 1) {
          IntVar[] array = support.dictionary.getVariableArray(expr.getIdent());
          objective =
              array != null && expr.getIndex() >= 0 && expr.getIndex() < array.length
                  ? array[expr.getIndex()]
                  : null;
        }
      }
    }
  }

  // the 0/1 variables of z = x[1] + ... + x[n] for the objective z, null otherwise
  private IntVar[] objectiveSum(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (a == null || a.length != x.length || c != 0 || x.length < MIN_VERTICES + 1) {
      return null;
    }
    int zAt = -1;
    for (int k = 0; k < x.length; k++) {
      if (x[k] == objective) {
        if (zAt >= 0) {
          return null;
        }
        zAt = k;
      }
    }
    if (zAt < 0 || (a[zAt] != 1 && a[zAt] != -1)) {
      return null;
    }
    int sign = -a[zAt];
    IntVar[] vertices = new IntVar[x.length - 1];
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    int m = 0;
    for (int k = 0; k < x.length; k++) {
      if (k == zAt) {
        continue;
      }
      if (a[k] != sign || !zeroOne(x[k]) || seen.put(source(x[k]), Boolean.TRUE) != null) {
        return null;
      }
      vertices[m++] = x[k];
    }
    return vertices.length <= MAX_VERTICES ? vertices : null;
  }

  private MaxCliqueBound post(IntVar[] vertices) {
    int n = vertices.length;
    Map<IntVar, Integer> index = vertexIndex(vertices);
    List<List<Integer>> conflicts = new ArrayList<>(n);
    for (int i = 0; i < n; i++) {
      conflicts.add(new ArrayList<>());
    }
    int found = 0;
    for (IntVar[] p : pairs) {
      Integer i = vertexOf(index, p[0]);
      Integer j = vertexOf(index, p[1]);
      if (i != null && j != null && !i.equals(j)) {
        conflicts.get(i).add(j);
        found++;
      }
    }
    if (found == 0) {
      return null;
    }
    int[][] lists = new int[n][];
    for (int i = 0; i < n; i++) {
      lists[i] = conflicts.get(i).stream().mapToInt(Integer::intValue).toArray();
    }
    MaxCliqueBound bound = new MaxCliqueBound(vertices, lists, objective);
    // redundant, so degree-based variable selections see the degrees of the model
    bound.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println(
          "% redundant max-clique bound over " + n + " vertices, " + found + " conflicts");
    }
    support.delayedConstraints.add(bound);
    return bound;
  }
}
