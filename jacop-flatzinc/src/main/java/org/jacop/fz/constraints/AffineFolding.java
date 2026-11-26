/*
 * AffineFolding.java
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

import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It folds a variable that is an affine function of another variable into the linear constraints
 * that use it, as the presolve of CP-SAT and of MIP solvers substitutes such variables out
 * (Achterberg, Bixby, Gu, Rothberg and Weninger, "Presolve reductions in mixed integer
 * programming", INFORMS Journal on Computing 32(2), 2020, free column substitution; Perron, Didier
 * and Gay, "The CP-SAT-LP solver", CP 2023). A variable z defined by {@code int_times(c, x, z)},
 * {@code int_plus(x, c, z)} or a two-term {@code int_lin_eq} with a unit coefficient on z, so that
 * z = p*x + q, whose every other occurrence is a term of a linear constraint ({@code int_lin_eq},
 * {@code int_lin_le}, {@code int_lin_ne}, reified or implied), is removed: each term a*z becomes
 * a*p*x and a*q moves to the constant, and the definition is not posted. MiniZinc leaves such
 * variables when it flattens a product by a constant inside a sum (nside of the MiniZinc Challenge
 * 2019: 56,889 of them, two thirds of the model).
 *
 * <p>The folding keeps every solution only when the domain of z allows each value p*x + q, so a
 * variable whose declared domain cuts that image stays. Variables of the solve item, output
 * variables, variables collected for channelling and those in any other constraint stay too, as
 * does a folding whose coefficients or constant would overflow. Off under {@code --proof}; the
 * system property {@code org.jacop.fz.affineFolding} set to false turns it off.
 *
 * <p>Only a variable in one row (besides its definition) is folded by default: one in several rows
 * is a shared sub-term, as the sub-sums {@link LinearOverlapDetector} introduces, and with lazy
 * clause generation the literals of its bounds carry what is learnt from one row to the others. The
 * system property {@code org.jacop.fz.affineFoldingRows} sets the number of rows.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class AffineFolding extends ModelRewrite {

  private static final String LIN_EQ = "int_lin_eq";

  private static final Set<String> ROWS =
      Set.of(
          LIN_EQ,
          "int_lin_le",
          "int_lin_ne",
          "int_lin_eq_reif",
          "int_lin_le_reif",
          "int_lin_ne_reif",
          "int_lin_eq_imp",
          "int_lin_le_imp",
          "int_lin_ne_imp");

  // the most rows a folded variable may occur in (org.jacop.fz.affineFoldingRows): with LCG a
  // variable in several rows learns better than its folded terms (code-generator mips_gobmk of
  // the 2019 Challenge: 7 variables in 49 rows, 15,451 -> 22,838 nodes when folded)
  private final int maxRows = Integer.getInteger("org.jacop.fz.affineFoldingRows", 1);

  // the image of x is checked value by value up to this many values, by its bounds above
  private static final int ENUMERATED = 10_000;

  /** A definition z = p*x + q by the constraint node. */
  private record Definition(ASTConstElem node, IntVar x, long p, long q) {}

  /**
   * It creates the folding.
   *
   * @param support the support of the FlatZinc front end.
   * @param kept the variables that must stay: those of the solve item and the output variables.
   */
  public AffineFolding(Support support, Set<IntVar> kept) {
    super(support, kept);
  }

  /**
   * It tells if the folding is on.
   *
   * @return false if the system property org.jacop.fz.affineFolding is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.affineFolding"));
  }

  /**
   * It folds the definitions of the model into its linear constraints.
   *
   * @param astTree the root of the parsed model.
   * @param skipped constraint nodes that are not posted.
   */
  public void detect(SimpleNode astTree, Set<SimpleNode> skipped) {
    List<ASTConstElem> all = FzItems.constraints(astTree, skipped);
    // the definitions first: the occurrences are read only when there is one (a clause model has
    // none, and the occurrences of its millions of clauses took seconds)
    List<Definition> definitions = new ArrayList<>();
    for (ASTConstElem c : all) {
      Definition d = definition(c);
      if (d != null) {
        definitions.add(d);
      }
    }
    if (definitions.isEmpty()) {
      return;
    }
    // the constraints each variable occurs in, and whether each constraint is a linear row
    Map<IntVar, Set<ASTConstElem>> occurrences = new IdentityHashMap<>();
    for (ASTConstElem c : all) {
      for (int k = 0; k < c.jjtGetNumChildren(); k++) {
        occur((SimpleNode) c.jjtGetChild(k), c, occurrences);
      }
    }
    Map<IntVar, Definition> folded = new IdentityHashMap<>();
    for (Definition d : definitions) {
      ASTConstElem c = d.node();
      if (!folded.containsKey(output(c, d)) && foldable(output(c, d), d, occurrences)) {
        folded.put(output(c, d), d);
      }
    }
    if (folded.isEmpty()) {
      return;
    }
    // an x that is itself folded would need its own definition: keep such z
    folded.values().removeIf(d -> folded.containsKey(d.x()));
    Set<ASTConstElem> rows = new HashSet<>();
    for (Map.Entry<IntVar, Definition> e : folded.entrySet()) {
      for (ASTConstElem c : occurrences.get(e.getKey())) {
        if (c != e.getValue().node()) {
          rows.add(c);
        }
      }
    }
    // rows whose folded form would overflow keep their variables, with their definitions
    Map<ASTConstElem, Row> rewritten = new IdentityHashMap<>();
    boolean changed = true;
    while (changed) {
      changed = false;
      rewritten.clear();
      for (ASTConstElem c : rows) {
        Row r = fold(c, folded);
        if (r == null) {
          // drop every z of the row and try again
          for (IntVar v : support.getVarArray((SimpleNode) c.jjtGetChild(1))) {
            changed |= folded.remove(v) != null;
          }
        } else {
          rewritten.put(c, r);
        }
      }
      if (changed) {
        rows.removeIf(c -> !mentions(c, folded));
      }
    }
    int index = 0;
    for (Map.Entry<ASTConstElem, Row> e : rewritten.entrySet()) {
      write(e.getKey(), e.getValue(), index++);
    }
    for (Map.Entry<IntVar, Definition> e : folded.entrySet()) {
      replaced.add(e.getValue().node());
      removed.add(e.getKey());
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% affine folding: "
              + folded.size()
              + " variables folded into "
              + rewritten.size()
              + " linear constraints");
    }
  }

  private boolean mentions(ASTConstElem c, Map<IntVar, Definition> folded) {
    for (IntVar v : support.getVarArray((SimpleNode) c.jjtGetChild(1))) {
      if (folded.containsKey(v)) {
        return true;
      }
    }
    return false;
  }

  // the defined variable of a definition
  private IntVar output(ASTConstElem c, Definition d) {
    String name = c.getName();
    if (name.equals(LIN_EQ)) {
      IntVar[] v = support.getVarArray((SimpleNode) c.jjtGetChild(1));
      return v[v[0] == d.x() ? 1 : 0];
    }
    return support.getVariable((ASTScalarFlatExpr) c.jjtGetChild(2));
  }

  // z = p*x + q from int_times(c, x, z), int_plus(x, c, z) or a*z + b*x = r with |a| = 1
  private Definition definition(ASTConstElem c) {
    String name = c.getName();
    if (name.equals("int_times") || name.equals("int_plus")) {
      if (!(c.jjtGetChild(0) instanceof ASTScalarFlatExpr a)
          || !(c.jjtGetChild(1) instanceof ASTScalarFlatExpr b)
          || !(c.jjtGetChild(2) instanceof ASTScalarFlatExpr z)
          || z.getType() == 0) {
        return null;
      }
      ASTScalarFlatExpr constant = null;
      if (a.getType() == 0) {
        constant = a;
      } else if (b.getType() == 0) {
        constant = b;
      }
      ASTScalarFlatExpr variable = constant == a ? b : a;
      if (constant == null || variable.getType() == 0) {
        return null;
      }
      long k = support.getInt(constant);
      IntVar x = support.getVariable(variable);
      if (name.equals("int_times")) {
        return k == 0 ? null : new Definition(c, x, k, 0);
      }
      return new Definition(c, x, 1, k);
    }
    if (name.equals(LIN_EQ)) {
      int[] a = support.getIntArray((SimpleNode) c.jjtGetChild(0));
      IntVar[] v = support.getVarArray((SimpleNode) c.jjtGetChild(1));
      if (a == null || a.length != 2 || v[0] == v[1]) {
        return null;
      }
      long r = support.getInt((ASTScalarFlatExpr) c.jjtGetChild(2));
      // the first term with a unit coefficient defines it: z = a*r - a*b*x since 1/a = a
      for (int t = 0; t < 2; t++) {
        if (Math.abs(a[t]) == 1 && a[1 - t] != 0) {
          return new Definition(c, v[1 - t], -a[t] * (long) a[1 - t], a[t] * r);
        }
      }
    }
    return null;
  }

  private boolean foldable(IntVar z, Definition d, Map<IntVar, Set<ASTConstElem>> occurrences) {
    IntVar x = d.x();
    if (z == x
        || z.singleton()
        || x.singleton()
        || kept.contains(z)
        || !support.reif.variablesOf(z).isEmpty()
        || !support.imply.variablesOf(z).isEmpty()
        || support.reif.size(z) > 0
        || support.imply.size(z) > 0) {
      return false;
    }
    int rows = 0;
    for (ASTConstElem c : occurrences.getOrDefault(z, Set.of())) {
      if (c != d.node() && !ROWS.contains(c.getName())) {
        return false;
      }
      if (c != d.node()) {
        rows++;
      }
    }
    if (rows > maxRows) {
      // a variable shared by several rows is a common sub-term: its literals carry what LCG learns
      // from one row to the others, as the sub-sums of LinearOverlapDetector do
      return false;
    }
    return covers(z.dom(), x.dom(), d.p(), d.q());
  }

  // whether every value p*v + q for v in dx is in dz
  private static boolean covers(IntDomain dz, IntDomain dx, long p, long q) {
    long a = p * dx.min() + q;
    long b = p * dx.max() + q;
    long lo = Math.min(a, b);
    long hi = Math.max(a, b);
    if (lo < IntDomain.MIN_INT || hi > IntDomain.MAX_INT) {
      return false;
    }
    if (dz.contains((int) lo, (int) hi)) {
      return true;
    }
    if (dx.getSize() > ENUMERATED) {
      return false;
    }
    for (ValueEnumeration e = dx.valueEnumeration(); e.hasMoreElements(); ) {
      if (!dz.contains((int) (p * e.nextElement() + q))) {
        return false;
      }
    }
    return true;
  }

  /** A linear constraint after folding: coefficients, variables and the new constant. */
  private static final class Row {
    private final int[] coefficients;
    private final IntVar[] vars;
    private final int constant;

    Row(int[] coefficients, IntVar[] vars, int constant) {
      this.coefficients = coefficients;
      this.vars = vars;
      this.constant = constant;
    }

    int[] coefficients() {
      return coefficients;
    }

    IntVar[] vars() {
      return vars;
    }

    int constant() {
      return constant;
    }
  }

  // the row with every folded z replaced, or null if a coefficient or the constant overflows
  private Row fold(ASTConstElem c, Map<IntVar, Definition> folded) {
    int[] a = support.getIntArray((SimpleNode) c.jjtGetChild(0));
    IntVar[] v = support.getVarArray((SimpleNode) c.jjtGetChild(1));
    long constant = support.getInt((ASTScalarFlatExpr) c.jjtGetChild(2));
    Map<IntVar, Long> terms = new LinkedHashMap<>();
    for (int i = 0; i < v.length; i++) {
      Definition d = folded.get(v[i]);
      if (d == null) {
        terms.merge(v[i], (long) a[i], Long::sum);
      } else {
        terms.merge(d.x(), a[i] * d.p(), Long::sum);
        constant -= a[i] * d.q();
      }
    }
    terms.values().removeIf(t -> t == 0);
    if (constant < IntDomain.MIN_INT || constant > IntDomain.MAX_INT || terms.isEmpty()) {
      return null;
    }
    int[] coefficients = new int[terms.size()];
    IntVar[] vars = new IntVar[terms.size()];
    int i = 0;
    for (Map.Entry<IntVar, Long> t : terms.entrySet()) {
      if (t.getValue() < IntDomain.MIN_INT || t.getValue() > IntDomain.MAX_INT) {
        return null;
      }
      coefficients[i] = t.getValue().intValue();
      vars[i++] = t.getKey();
    }
    return new Row(coefficients, vars, (int) constant);
  }

  // the folded row in place of the arguments of the constraint, which every later reader sees
  private void write(ASTConstElem c, Row r, int index) {
    SimpleNode literal = new SimpleNode(JJTARRAYLITERAL);
    for (int i = 0; i < r.coefficients().length; i++) {
      literal.jjtAddChild(constant(r.coefficients()[i], literal), i);
    }
    literal.jjtSetParent(c);
    c.jjtAddChild(literal, 0);
    // an identity of the model of that name would be replaced by the folded row for every later
    // reader of its array
    String ident = "X_JACOP_AFFINE_" + index;
    while (support.dictionary.isIdentifier(ident)) {
      ident += "_";
    }
    support.dictionary.addVariableArray(ident, r.vars());
    ASTScalarFlatExpr array = new ASTScalarFlatExpr(JJTSCALARFLATEXPR);
    array.setType(2);
    array.setIdent(ident);
    array.jjtSetParent(c);
    c.jjtAddChild(array, 1);
    c.jjtAddChild(constant(r.constant(), c), 2);
  }

  private static ASTScalarFlatExpr constant(int value, SimpleNode parent) {
    ASTScalarFlatExpr e = new ASTScalarFlatExpr(JJTSCALARFLATEXPR);
    e.setType(0);
    e.setInt(value);
    e.jjtSetParent(parent);
    return e;
  }

  private void occur(SimpleNode arg, ASTConstElem c, Map<IntVar, Set<ASTConstElem>> occurrences) {
    if (arg.getId() == JJTARRAYLITERAL) {
      for (int i = 0; i < arg.jjtGetNumChildren(); i++) {
        occur((SimpleNode) arg.jjtGetChild(i), c, occurrences);
      }
      return;
    }
    if (!(arg instanceof ASTScalarFlatExpr e)) {
      return;
    }
    for (IntVar v : FzItems.variables(support, e)) {
      if (v != null && !v.singleton()) {
        occurrences.computeIfAbsent(v, x -> new Occurrences()).add(c);
      }
    }
  }

  /**
   * The constraints a variable occurs in, in the order they are read. The arguments of one
   * constraint are read one after the other, so a constraint is a repeat only of the last one
   * added. A HashSet for each variable (with its map and table) took 250 MB of the 1.46 million
   * Boolean variables of XCSP 2022 RoomMate-sr0700 while the model was read.
   */
  static final class Occurrences extends AbstractSet<ASTConstElem> {
    private ASTConstElem[] elements = new ASTConstElem[2];
    private int size;

    @Override
    public boolean add(ASTConstElem c) {
      if (size > 0 && elements[size - 1] == c) {
        return false;
      }
      if (size == elements.length) {
        elements = Arrays.copyOf(elements, 2 * size);
      }
      elements[size++] = c;
      return true;
    }

    @Override
    public Iterator<ASTConstElem> iterator() {
      return Arrays.asList(elements).subList(0, size).iterator();
    }

    @Override
    public int size() {
      return size;
    }

    // equal to any set with the same constraints, as a set is
    @Override
    public boolean equals(Object o) {
      return o instanceof Set<?> other && other.size() == size && containsAll(other);
    }

    @Override
    public int hashCode() {
      int h = 0;
      for (int k = 0; k < size; k++) {
        h += elements[k].hashCode();
      }
      return h;
    }
  }
}
