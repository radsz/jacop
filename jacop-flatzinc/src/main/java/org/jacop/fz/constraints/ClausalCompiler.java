/*
 * ClausalCompiler.java
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
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * Compiles a satisfaction model over small domains into one CNF for JaSAT, as the SAT-encoding
 * solvers that decide most instances of the CSP track of the XCSP competitions do (Picat-SAT: Zhou
 * and Kjellerstrand, "Optimizing SAT Encodings for Arithmetic Constraints", CP 2017; Kat and sCOP:
 * Soh, Banbara and Tamura, "Proposal and Evaluation of Hybrid Encoding of CSP to SAT Integrating
 * Order and Log Encodings", IJAIT 2017).
 *
 * <p>An integer variable that a constraint compares by order (a sum of one or two terms, a product,
 * a comparison, a count, lex, max, min, increasing) gets order literals {@code [x >= d]} for the
 * values of its domain but the first, chained, and direct literals {@code [x = d]} defined from
 * them (Tamura, Taga, Kitagawa and Banbara, "Compiling finite linear CSP into SAT", Constraints 14,
 * 2009). A variable that appears only in tables, all-different, the lists of counts and sums of
 * three or more terms gets direct literals only, with at-least-one and pairwise at-most-one clauses
 * (the direct encoding, de Kleer 1989; Walsh, "SAT v CSP", CP 2000), so the SAT solver does not
 * branch on order literals no constraint reads. Binary tables get the support encoding (Kasif 1990;
 * Gent, "Arc Consistency in SAT", ECAI 2002), on which unit propagation keeps arc consistency;
 * other tables get one selector literal per tuple. Products get support clauses over direct
 * literals, once the value sets of products of products are narrowed by multiplying the value sets
 * of their factors. Sums of one or two terms become order-encoding clauses; longer sums become a
 * multi-valued decision diagram over their partial sums whose nodes are literals defined both ways
 * (Abio, Nieuwenhuis, Oliveras, Rodriguez-Carbonell and Mayer-Eichberger, "A New Look at BDDs for
 * Pseudo-Boolean Constraints", JAIR 45, 2012); a sum whose diagram would be too large becomes
 * binary adders (the log encoding of Picat-SAT). All-different, counts, regular, tables, lex chains
 * and value precedence get their usual clausal definitions, so an unsatisfiability proof of the CNF
 * is one of the model.
 *
 * <p>The compiler takes a model only when each constraint is of a kind it compiles, each integer
 * variable has at most {@code org.jacop.fz.clausal.maxDomain} values (default 64), the variables of
 * regular constraints at most {@code org.jacop.fz.clausal.regularDomain} values (default 3: lazy
 * clause generation is faster on RotatingWorkforce2 and NurseRostering), and the CNF has at most
 * {@code org.jacop.fz.clausal.maxClauses} clauses (default 2,000,000: CarSequencing, Primes and the
 * large Crosswords are faster with lazy clause generation). {@code
 * org.jacop.fz.clausal.direct=false} gives every variable order literals. The system property
 * {@code org.jacop.fz.clausal=false} turns the compilation off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ClausalCompiler {

  private static final String ALLDIFF = "jacop_alldiff";
  private static final String ALLDISTINCT = "jacop_alldistinct";
  private static final String COUNT_VALUES = "jacop_count_values";
  private static final String AMONG = "jacop_among";
  private static final String INCREASING = "jacop_increasing";
  private static final String SHORT_TABLE_INT = "jacop_short_table_int";
  private static final String TABLE_INT = "jacop_table_int";
  private static final String NEGATIVE_TABLE_INT = "jacop_negative_table_int";

  /** The constraints the compiler encodes. */
  static final Set<String> SUPPORTED =
      Set.of(
          "int_times",
          "int_lin_eq",
          "int_lin_le",
          "int_lin_ne",
          "int_lin_eq_reif",
          "int_lin_le_reif",
          "int_lin_ne_reif",
          "int_lin_eq_imp",
          "int_lin_le_imp",
          "int_lin_ne_imp",
          "int_eq",
          "int_ne",
          "int_le",
          "int_lt",
          "int_eq_reif",
          "int_ne_reif",
          "int_le_reif",
          "int_lt_reif",
          "int_eq_imp",
          "int_ne_imp",
          "int_le_imp",
          "int_lt_imp",
          "bool2int",
          "bool_clause",
          "array_bool_or",
          "array_bool_and",
          "bool_eq",
          "bool_not",
          "bool_le",
          "bool_lt",
          "bool_xor",
          "bool_eq_reif",
          "bool_ne_reif",
          ALLDIFF,
          ALLDISTINCT,
          COUNT_VALUES,
          AMONG,
          INCREASING,
          "jacop_strictly_increasing",
          "jacop_maximum",
          "jacop_minimum",
          "jacop_lex_chain_lesseq_int",
          "jacop_value_precede_chain_int",
          SHORT_TABLE_INT,
          TABLE_INT,
          NEGATIVE_TABLE_INT,
          "jacop_regular_set");

  /** Values a domain may have for its literals to be enumerated at all. */
  private static final int ENUMERATED = 1_000_000;

  /**
   * Returns whether the compilation is on, the property {@code org.jacop.fz.clausal}.
   *
   * @return true unless the property is false
   */
  public static boolean enabled() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.clausal", "true"));
  }

  /**
   * Returns the largest domain a variable of a compiled model may have, the property {@code
   * org.jacop.fz.clausal.maxDomain}.
   *
   * @return the number of values, 64 by default
   */
  public static int maxDomain() {
    return Integer.getInteger("org.jacop.fz.clausal.maxDomain", 64);
  }

  /**
   * Returns the largest domain a variable of a regular constraint of a compiled model may have, the
   * property {@code org.jacop.fz.clausal.regularDomain}.
   *
   * @return the number of values, 3 by default
   */
  static int regularDomain() {
    return Integer.getInteger("org.jacop.fz.clausal.regularDomain", 3);
  }

  /**
   * Returns whether variables that only appear in value constraints (tables, alldifferent, the
   * counted lists of count and among) get direct literals without order literals, the property
   * {@code org.jacop.fz.clausal.direct}.
   *
   * @return true unless the property is false
   */
  static boolean direct() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.clausal.direct", "true"));
  }

  /**
   * Returns the largest number of clauses of a compiled model, the property {@code
   * org.jacop.fz.clausal.maxClauses}: larger CNFs (CarSequencing, Primes, big Crosswords) are
   * solved faster by the CP side.
   *
   * @return the number of clauses, 2,000,000 by default
   */
  static long maxClauses() {
    return Long.getLong("org.jacop.fz.clausal.maxClauses", 2_000_000L);
  }

  private static long maxLiterals() {
    return Long.getLong("org.jacop.fz.clausal.maxLiterals", 60_000_000L);
  }

  private static int mddLimit() {
    return Integer.getInteger("org.jacop.fz.clausal.mddNodes", 200_000);
  }

  /** A model the compiler does not take; the compilation stops. */
  private static final class NotCompiled extends RuntimeException {
    private static final long serialVersionUID = 1L;

    NotCompiled(String reason) {
      super(reason, null, false, false);
    }
  }

  private final Support support;
  private final int maxDomain;
  private final int regularDomain;
  private final boolean direct;
  // variables that need order literals; the others are encoded with direct literals only
  private final Set<IntVar> ordered = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
  private final long maxLits;
  private final long maxClauses;
  private final int mddNodes;

  // the clauses, each followed by a 0
  private int[] buf = new int[1 << 16];
  private int size;
  private int clauses;
  private int numVars = 1;
  private static final int T = 1;
  private static final int F = -1;

  // the encoding of each variable
  private final Map<IntVar, Enc> enc = new IdentityHashMap<>();
  // the value sets narrowed by products
  private final Map<IntVar, int[]> narrowed = new IdentityHashMap<>();

  // a variable has a value other than 0 and 1 (models of 0/1 variables stay with LCG, or are
  // pure clause models already)
  private boolean arithmetic;

  // statistics
  private int mdds;
  private int logs;

  private ClausalCompiler(Support support) {
    this.support = support;
    this.maxDomain = maxDomain();
    this.regularDomain = regularDomain();
    this.direct = direct();
    this.maxLits = maxLiterals();
    this.maxClauses = maxClauses();
    this.mddNodes = mddLimit();
    add(T);
  }

  /**
   * Compiles the constraints of a model into clauses, or returns null when the model has a
   * constraint the compiler does not encode or a variable with a larger domain than allowed.
   *
   * @param support the support of the front end, which reads the variables and arrays
   * @param astTree the parsed model
   * @return the clauses and the literals of the values of each variable, or null
   */
  public static ClausalModel compile(Support support, SimpleNode astTree) {
    long start = System.nanoTime();
    List<ASTConstElem> items = new ArrayList<>();
    String[] unsupported = {null};
    support.forEachConstraint(
        astTree,
        node -> {
          if (unsupported[0] == null && !SUPPORTED.contains(node.getName())) {
            unsupported[0] = node.getName();
          }
          items.add(node);
        });
    if (unsupported[0] != null || items.isEmpty()) {
      if (support.options.debug()) {
        FzConsole.println("% clausal compilation: not taken, constraint " + unsupported[0]);
      }
      return null;
    }
    ClausalCompiler c = new ClausalCompiler(support);
    try {
      // the variables no product narrows first: NumberPartitioning-260 of XCSP 2022 spent 6 s
      // narrowing 259 squares of 131-value factors before a factor was found too large
      c.checkDomains(items, c.productResults(items));
      c.narrowProducts(items);
      c.checkDomains(items, Set.of());
      c.orderedVariables(items);
      if (!c.arithmetic) {
        throw new NotCompiled("0/1 variables only");
      }
      for (ASTConstElem item : items) {
        c.compile(item);
      }
    } catch (NotCompiled e) {
      if (support.options.debug()) {
        FzConsole.println("% clausal compilation: not taken, " + e.getMessage());
      }
      return null;
    }
    ClausalModel model = c.model();
    if (support.options.debug()) {
      FzConsole.println(
          "% clausal compilation: "
              + model.numVars()
              + " variables, "
              + c.clauses
              + " clauses, "
              + c.mdds
              + " diagrams, "
              + c.logs
              + " adders, "
              + (System.nanoTime() - start) / 1_000_000
              + " ms");
    }
    return model;
  }

  private ClausalModel model() {
    List<IntVar> vars = new ArrayList<>(enc.size());
    List<int[]> values = new ArrayList<>(enc.size());
    List<int[]> lits = new ArrayList<>(enc.size());
    for (Map.Entry<IntVar, Enc> e : enc.entrySet()) {
      vars.add(e.getKey());
      values.add(e.getValue().vals);
      lits.add(e.getValue().eq);
    }
    return new ClausalModel(numVars, Arrays.copyOf(buf, size), vars, values, lits);
  }

  // ---------------------------------------------------------------- clauses

  private int newVar() {
    return ++numVars;
  }

  private void add(int... c) {
    addClause(c, c.length);
  }

  private void addClause(int[] c, int n) {
    int k = 0;
    for (int i = 0; i < n; i++) {
      if (c[i] == T) {
        return;
      }
    }
    if (size + n + 1 > buf.length) {
      if (size + n + 1 > maxLits) {
        throw new NotCompiled("more than " + maxLits + " literals");
      }
      buf = Arrays.copyOf(buf, (int) Math.min(Math.max(2L * buf.length, size + n + 1L), maxLits));
    }
    for (int i = 0; i < n; i++) {
      if (c[i] != F) {
        buf[size + k++] = c[i];
      }
    }
    buf[size + k] = 0;
    size += k + 1;
    if (++clauses > maxClauses) {
      throw new NotCompiled("more than " + maxClauses + " clauses");
    }
  }

  private void add(List<Integer> c) {
    int[] a = new int[c.size()];
    for (int i = 0; i < a.length; i++) {
      a[i] = c.get(i);
    }
    addClause(a, a.length);
  }

  private int and(int... lits) {
    int n = 0;
    int[] l = new int[lits.length];
    for (int x : lits) {
      if (x == F) {
        return F;
      }
      if (x != T) {
        l[n++] = x;
      }
    }
    if (n == 0) {
      return T;
    }
    if (n == 1) {
      return l[0];
    }
    int o = newVar();
    int[] big = new int[n + 1];
    big[0] = o;
    for (int i = 0; i < n; i++) {
      add(-o, l[i]);
      big[i + 1] = -l[i];
    }
    add(big);
    return o;
  }

  private int or(int... lits) {
    int[] neg = new int[lits.length];
    for (int i = 0; i < lits.length; i++) {
      neg[i] = -lits[i];
    }
    return -and(neg);
  }

  private int xor3(int a, int b, int c) {
    int s = newVar();
    for (int x = 0; x < 2; x++) {
      for (int y = 0; y < 2; y++) {
        for (int z = 0; z < 2; z++) {
          add(x == 1 ? -a : a, y == 1 ? -b : b, z == 1 ? -c : c, ((x ^ y ^ z) == 1) ? s : -s);
        }
      }
    }
    return s;
  }

  private int maj(int a, int b, int c) {
    int m = newVar();
    int[][] pairs = {{a, b}, {a, c}, {b, c}};
    for (int[] p : pairs) {
      add(-p[0], -p[1], m);
      add(p[0], p[1], -m);
    }
    return m;
  }

  // at most one of the literals: pairwise up to 6, else a sequential counter
  private void atMostOne(int[] lits) {
    int[] l = Arrays.stream(lits).filter(x -> x != F).toArray();
    if (l.length <= 1) {
      return;
    }
    if (l.length <= 6) {
      for (int i = 0; i < l.length; i++) {
        for (int j = i + 1; j < l.length; j++) {
          add(-l[i], -l[j]);
        }
      }
      return;
    }
    int prev = 0;
    for (int i = 0; i < l.length; i++) {
      if (i == l.length - 1) {
        add(-prev, -l[i]);
        break;
      }
      int s = newVar();
      add(-l[i], s);
      if (prev != 0) {
        add(-prev, s);
        add(-prev, -l[i]);
      }
      prev = s;
    }
  }

  // ---------------------------------------------------------------- variables

  /** The order and direct literals of a variable. */
  private static final class Enc {
    final int[] vals;
    // ge[i]: x >= vals[i] (ge[0] is TRUE)
    final int[] ge;
    final int[] eq;

    Enc(int[] vals, int[] ge, int[] eq) {
      this.vals = vals;
      this.ge = ge;
      this.eq = eq;
    }

    int lo() {
      return vals[0];
    }

    int hi() {
      return vals[vals.length - 1];
    }

    int size() {
      return vals.length;
    }

    int ge(int v) {
      if (ge == null) {
        throw new NotCompiled("order literal of a direct variable");
      }
      if (v <= vals[0]) {
        return T;
      }
      if (v > vals[vals.length - 1]) {
        return F;
      }
      int i = Arrays.binarySearch(vals, v);
      return ge[i >= 0 ? i : -i - 1];
    }

    int le(int v) {
      return -ge(v + 1);
    }

    int eq(int v) {
      int i = Arrays.binarySearch(vals, v);
      return i >= 0 ? eq[i] : F;
    }

    boolean has(int v) {
      return Arrays.binarySearch(vals, v) >= 0;
    }
  }

  private int[] values(IntVar x) {
    int[] n = narrowed.get(x);
    if (n != null) {
      return n;
    }
    IntDomain d = x.domain;
    if (d.getSize() > ENUMERATED) {
      return null;
    }
    int[] v = new int[d.getSize()];
    int i = 0;
    for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
      v[i++] = e.nextElement();
    }
    return v;
  }

  private Enc enc(IntVar x) {
    Enc e = enc.get(x);
    if (e != null) {
      return e;
    }
    int[] d = values(x);
    if (d == null || d.length > Math.max(maxDomain, 2) && !x.singleton()) {
      throw new NotCompiled("domain of " + x.id() + " too large");
    }
    if (d.length == 0) {
      add();
      d = new int[] {0};
    }
    int n = d.length;
    if (direct && n > 2 && !ordered.contains(x)) {
      int[] eq = new int[n];
      for (int i = 0; i < n; i++) {
        eq[i] = newVar();
      }
      add(eq);
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          add(-eq[i], -eq[j]);
        }
      }
      e = new Enc(d, null, eq);
      enc.put(x, e);
      return e;
    }
    int[] ge = new int[n];
    ge[0] = T;
    for (int i = 1; i < n; i++) {
      ge[i] = newVar();
    }
    for (int i = 1; i < n - 1; i++) {
      add(-ge[i + 1], ge[i]);
    }
    int[] eq = new int[n];
    for (int i = 0; i < n; i++) {
      if (n == 1) {
        eq[i] = T;
      } else if (i == 0) {
        eq[i] = -ge[1];
      } else if (i == n - 1) {
        eq[i] = ge[i];
      } else {
        int o = newVar();
        add(-o, ge[i]);
        add(-o, -ge[i + 1]);
        add(o, -ge[i], ge[i + 1]);
        eq[i] = o;
      }
    }
    e = new Enc(d, ge, eq);
    enc.put(x, e);
    return e;
  }

  private int lit(IntVar b) {
    Enc e = enc(b);
    if (e.lo() < 0 || e.hi() > 1) {
      throw new NotCompiled("Boolean " + b.id() + " not 0/1");
    }
    return e.eq(1);
  }

  // ---------------------------------------------------------------- arguments

  private IntVar[] vars(ASTConstElem node, int i) {
    return support.getVarArray((SimpleNode) node.jjtGetChild(i));
  }

  private IntVar var(ASTConstElem node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private int[] ints(ASTConstElem node, int i) {
    return support.getIntArray((SimpleNode) node.jjtGetChild(i));
  }

  private int integer(ASTConstElem node, int i) {
    return support.getInt((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private int[] set(ASTConstElem node, int i) {
    IntDomain d = support.getSetLiteral(node, i);
    int[] v = new int[d.getSize()];
    int k = 0;
    for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
      v[k++] = e.nextElement();
    }
    return v;
  }

  // ---------------------------------------------------------------- domains

  // the value set of each product of two factors with known value sets
  private void narrowProducts(List<ASTConstElem> items) {
    for (int round = 0; round < 10; round++) {
      boolean changed = false;
      for (ASTConstElem item : items) {
        if (!"int_times".equals(item.getName())) {
          continue;
        }
        IntVar a = var(item, 0);
        IntVar b = var(item, 1);
        IntVar z = var(item, 2);
        int[] da = values(a);
        int[] db = values(b);
        if (da == null || db == null || (long) da.length * db.length > 200_000) {
          continue;
        }
        TreeSet<Integer> prod = new TreeSet<>();
        for (int x : da) {
          for (int y : db) {
            long p = (long) x * y;
            if (z.domain.contains((int) p) && p == (int) p) {
              prod.add((int) p);
            }
          }
        }
        int[] old = values(z);
        int[] nd = prod.stream().mapToInt(Integer::intValue).toArray();
        if (old != null) {
          nd = Arrays.stream(nd).filter(v -> Arrays.binarySearch(old, v) >= 0).toArray();
        }
        if (old == null || nd.length != old.length) {
          narrowed.put(z, nd);
          changed = true;
        }
      }
      if (!changed) {
        break;
      }
    }
  }

  /** The constraints whose variables are only compared with values, through direct literals. */
  private static final Set<String> VALUE_ONLY =
      Set.of(
          TABLE_INT,
          SHORT_TABLE_INT,
          NEGATIVE_TABLE_INT,
          ALLDIFF,
          ALLDISTINCT,
          COUNT_VALUES,
          AMONG);

  private void orderedVariables(List<ASTConstElem> items) {
    for (ASTConstElem item : items) {
      String name = item.getName();
      if (name.startsWith("int_lin_") && longSum(item)) {
        // a sum of three or more terms is a diagram or adders over direct literals
        continue;
      }
      if (!VALUE_ONLY.contains(name)) {
        for (int i = 0; i < item.jjtGetNumChildren(); i++) {
          ordered.addAll(Arrays.asList(argumentVars(item, i)));
        }
      } else if (name.equals(COUNT_VALUES) || name.equals(AMONG)) {
        // the counts are compared by order
        ordered.addAll(Arrays.asList(argumentVars(item, 2)));
      }
    }
  }

  private boolean longSum(ASTConstElem item) {
    int[] a = ints(item, 0);
    IntVar[] xs = vars(item, 1);
    int terms = 0;
    for (int i = 0; i < xs.length; i++) {
      terms += a[i] != 0 && !xs[i].singleton() ? 1 : 0;
    }
    return terms >= 3;
  }

  private IntVar[] argumentVars(ASTConstElem item, int i) {
    SimpleNode child = (SimpleNode) item.jjtGetChild(i);
    if (child instanceof ASTScalarFlatExpr s && (s.getType() == 2 || s.getType() == 3)) {
      IntVar v = support.dictionary.getVariable(s.getIdent());
      if (v != null && s.getType() == 2) {
        return new IntVar[] {v};
      }
      IntVar[] array = support.dictionary.getVariableArray(s.getIdent());
      return array != null ? array : new IntVar[0];
    }
    if (child.getId() == JJTARRAYLITERAL_ID && isVarArray(child)) {
      return support.getVarArray(child);
    }
    return new IntVar[0];
  }

  // the results of the products, whose value sets narrowProducts narrows
  private Set<IntVar> productResults(List<ASTConstElem> items) {
    Set<IntVar> z = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
    for (ASTConstElem item : items) {
      if ("int_times".equals(item.getName())) {
        z.add(var(item, 2));
      }
    }
    return z;
  }

  // every variable but those skipped has at most maxDomain values
  private void checkDomains(List<ASTConstElem> items, Set<IntVar> skip) {
    for (ASTConstElem item : items) {
      for (int i = 0; i < item.jjtGetNumChildren(); i++) {
        SimpleNode child = (SimpleNode) item.jjtGetChild(i);
        IntVar[] vs = null;
        if (child instanceof ASTScalarFlatExpr s && (s.getType() == 2 || s.getType() == 3)) {
          IntVar v = support.dictionary.getVariable(s.getIdent());
          if (v != null && s.getType() == 2) {
            vs = new IntVar[] {v};
          } else if (support.dictionary.getVariableArray(s.getIdent()) != null) {
            vs = support.dictionary.getVariableArray(s.getIdent());
          }
        } else if (child.getId() == JJTARRAYLITERAL_ID && isVarArray(child)) {
          vs = support.getVarArray(child);
        }
        if (vs == null) {
          continue;
        }
        for (IntVar v : vs) {
          if (v.singleton() || skip.contains(v)) {
            continue;
          }
          int[] d = values(v);
          if (d == null || d.length > maxDomain) {
            throw new NotCompiled("domain of " + v.id() + " too large");
          }
          arithmetic |= d.length > 0 && (d[0] < 0 || d[d.length - 1] > 1);
        }
      }
    }
  }

  private static final int JJTARRAYLITERAL_ID = org.jacop.fz.ParserTreeConstants.JJTARRAYLITERAL;

  private boolean isVarArray(SimpleNode node) {
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      if (node.jjtGetChild(i) instanceof ASTScalarFlatExpr s
          && (s.getType() == 2 || s.getType() == 3)) {
        return true;
      }
    }
    return false;
  }

  // ---------------------------------------------------------------- constraints

  private void compile(ASTConstElem n) {
    switch (n.getName()) {
      case "int_times" -> times(var(n, 0), var(n, 1), var(n, 2));
      case "int_lin_eq",
          "int_lin_le",
          "int_lin_ne",
          "int_lin_eq_reif",
          "int_lin_le_reif",
          "int_lin_ne_reif",
          "int_lin_eq_imp",
          "int_lin_le_imp",
          "int_lin_ne_imp" ->
          linear(n);
      case "int_eq", "int_ne", "int_le", "int_lt" -> binary(n, 0, false);
      case "int_eq_reif", "int_ne_reif", "int_le_reif", "int_lt_reif" ->
          binary(n, lit(var(n, 2)), false);
      case "int_eq_imp", "int_ne_imp", "int_le_imp", "int_lt_imp" ->
          binary(n, lit(var(n, 2)), true);
      case "bool2int" -> {
        int b = lit(var(n, 0));
        Enc x = enc(var(n, 1));
        add(-b, x.eq(1));
        add(b, x.eq(0));
      }
      case "bool_clause" -> {
        IntVar[] p = vars(n, 0);
        IntVar[] q = vars(n, 1);
        int[] c = new int[p.length + q.length];
        for (int i = 0; i < p.length; i++) {
          c[i] = lit(p[i]);
        }
        for (int i = 0; i < q.length; i++) {
          c[p.length + i] = -lit(q[i]);
        }
        add(c);
      }
      case "array_bool_or", "array_bool_and" -> {
        IntVar[] xs = vars(n, 0);
        int r = lit(var(n, 1));
        int[] l = new int[xs.length];
        for (int i = 0; i < xs.length; i++) {
          l[i] = lit(xs[i]);
        }
        equivalent(r, "array_bool_or".equals(n.getName()) ? or(l) : and(l));
      }
      case "bool_eq" -> equivalent(lit(var(n, 0)), lit(var(n, 1)));
      case "bool_not" -> equivalent(lit(var(n, 0)), -lit(var(n, 1)));
      case "bool_le" -> add(-lit(var(n, 0)), lit(var(n, 1)));
      case "bool_lt" -> {
        add(-lit(var(n, 0)));
        add(lit(var(n, 1)));
      }
      case "bool_xor", "bool_ne_reif" ->
          equivalent(-lit(var(n, 2)), equalLit(lit(var(n, 0)), lit(var(n, 1))));
      case "bool_eq_reif" -> equivalent(lit(var(n, 2)), equalLit(lit(var(n, 0)), lit(var(n, 1))));
      case ALLDIFF, ALLDISTINCT -> alldiff(vars(n, 0));
      case COUNT_VALUES -> {
        IntVar[] xs = vars(n, 0);
        int[] cover = ints(n, 1);
        IntVar[] counts = vars(n, 2);
        for (int j = 0; j < cover.length; j++) {
          int[] l = new int[xs.length];
          for (int i = 0; i < xs.length; i++) {
            l[i] = enc(xs[i]).eq(cover[j]);
          }
          countEq(l, enc(counts[j]));
        }
      }
      case AMONG -> {
        IntVar[] xs = vars(n, 0);
        int[] s = set(n, 1);
        int[] l = new int[xs.length];
        for (int i = 0; i < xs.length; i++) {
          Enc e = enc(xs[i]);
          List<Integer> in = new ArrayList<>();
          for (int v : s) {
            if (e.has(v)) {
              in.add(e.eq(v));
            }
          }
          l[i] = or(in.stream().mapToInt(Integer::intValue).toArray());
        }
        countEq(l, enc(var(n, 2)));
      }
      case INCREASING, "jacop_strictly_increasing" -> {
        IntVar[] xs = vars(n, 0);
        int gap = n.getName().equals(INCREASING) ? 0 : -1;
        for (int i = 0; i + 1 < xs.length; i++) {
          linear(new int[] {1, -1}, new IntVar[] {xs[i], xs[i + 1]}, Op.LE, gap, 0, false);
        }
      }
      case "jacop_maximum", "jacop_minimum" -> extremum(n);
      case "jacop_lex_chain_lesseq_int" -> {
        IntVar[] xs = vars(n, 0);
        int cols = integer(n, 1);
        // no vectors (cols 0) give no pairs
        int rows = cols == 0 ? 0 : xs.length / cols;
        Enc[][] vec = new Enc[cols][rows];
        for (int j = 0; j < cols; j++) {
          for (int i = 0; i < rows; i++) {
            vec[j][i] = enc(xs[i * cols + j]);
          }
        }
        for (int j = 0; j + 1 < cols; j++) {
          lexLe(vec[j], vec[j + 1]);
        }
      }
      case "jacop_value_precede_chain_int" -> precede(ints(n, 0), vars(n, 1));
      case SHORT_TABLE_INT -> table(vars(n, 0), ints(n, 1), integer(n, 2), true);
      case TABLE_INT -> table(vars(n, 0), ints(n, 1), 0, false);
      case NEGATIVE_TABLE_INT -> {
        IntVar[] xs = vars(n, 0);
        int[] t = ints(n, 1);
        int k = xs.length;
        // a table without columns has no rows
        for (int r = 0; k > 0 && r + k <= t.length; r += k) {
          int[] c = new int[k];
          for (int i = 0; i < k; i++) {
            c[i] = -enc(xs[i]).eq(t[r + i]);
          }
          add(c);
        }
      }
      case "jacop_regular_set" -> regular(n);
      default -> throw new NotCompiled(n.getName());
    }
  }

  private void equivalent(int a, int b) {
    add(-a, b);
    add(a, -b);
  }

  private int equalLit(int a, int b) {
    int e = newVar();
    add(-e, -a, b);
    add(-e, a, -b);
    add(e, a, b);
    add(e, -a, -b);
    return e;
  }

  // r is 0 for a constraint that must hold; imp: r implies the constraint, else r iff it holds
  private void link(int p, int r, boolean imp) {
    add(-r, p);
    if (!imp) {
      add(r, -p);
    }
  }

  private void binary(ASTConstElem n, int r, boolean imp) {
    String name = n.getName();
    IntVar x = var(n, 0);
    IntVar y = var(n, 1);
    Op op;
    int k = 0;
    if (name.startsWith("int_eq")) {
      op = Op.EQ;
    } else if (name.startsWith("int_ne")) {
      op = Op.NE;
    } else if (name.startsWith("int_le")) {
      op = Op.LE;
    } else {
      op = Op.LE;
      k = -1;
    }
    linear(new int[] {1, -1}, new IntVar[] {x, y}, op, k, r, imp);
  }

  private void times(IntVar a, IntVar b, IntVar z) {
    Enc ea = enc(a);
    Enc eb = enc(b);
    Enc ez = enc(z);
    for (int i = 0; i < ea.size(); i++) {
      for (int j = 0; j < eb.size(); j++) {
        long p = (long) ea.vals[i] * eb.vals[j];
        add(-ea.eq[i], -eb.eq[j], p == (int) p ? ez.eq((int) p) : F);
      }
    }
    supportProducts(ea, eb, ez);
    supportProducts(eb, ea, ez);
  }

  // a = va and z = w imply b in {vb : va * vb = w}
  private void supportProducts(Enc ea, Enc eb, Enc ez) {
    for (int i = 0; i < ea.size(); i++) {
      for (int w = 0; w < ez.size(); w++) {
        List<Integer> c = new ArrayList<>();
        c.add(-ea.eq[i]);
        c.add(-ez.eq[w]);
        for (int j = 0; j < eb.size(); j++) {
          if ((long) ea.vals[i] * eb.vals[j] == ez.vals[w]) {
            c.add(eb.eq[j]);
          }
        }
        add(c);
      }
    }
  }

  private void alldiff(IntVar[] xs) {
    Enc[] e = new Enc[xs.length];
    TreeSet<Integer> all = new TreeSet<>();
    for (int i = 0; i < xs.length; i++) {
      e[i] = enc(xs[i]);
      for (int v : e[i].vals) {
        all.add(v);
      }
    }
    for (int v : all) {
      List<Integer> l = new ArrayList<>();
      for (Enc x : e) {
        if (x.has(v)) {
          l.add(x.eq(v));
        }
      }
      int[] a = l.stream().mapToInt(Integer::intValue).toArray();
      atMostOne(a);
      if (all.size() == xs.length) {
        add(a);
      }
    }
  }

  // the number of true literals is y
  private void countEq(int[] lits, Enc y) {
    int nt = 0;
    List<Integer> l = new ArrayList<>();
    for (int x : lits) {
      if (x == T) {
        nt++;
      } else if (x != F) {
        l.add(x);
      }
    }
    int top = y.hi() - nt + 1;
    // s[j]: at least j of the literals so far, j = 1..len
    int[] s = new int[0];
    for (int x : l) {
      int len = Math.min(s.length + 1, Math.max(top, 0));
      int[] ns = new int[len];
      for (int j = 1; j <= len; j++) {
        int a = j <= s.length ? s[j - 1] : F;
        int b = j == 1 ? T : s[j - 2];
        int o = newVar();
        add(-a, o);
        add(-b, -x, o);
        add(-o, a, b);
        add(-o, a, x);
        ns[j - 1] = o;
      }
      s = ns;
    }
    for (int i = 1; i < y.size(); i++) {
      int j = y.vals[i] - nt;
      int atLeast = j <= 0 ? T : (j <= s.length ? s[j - 1] : F);
      equivalent(y.ge[i], atLeast);
    }
    int lo = y.lo() - nt;
    if (lo > 0) {
      add(lo <= s.length ? s[lo - 1] : F);
    }
    if (top <= 0) {
      add();
    } else if (top <= s.length) {
      add(-s[top - 1]);
    }
  }

  private void extremum(ASTConstElem n) {
    boolean max = "jacop_maximum".equals(n.getName());
    Enc z = enc(var(n, 0));
    IntVar[] xs = vars(n, 1);
    Enc[] e = new Enc[xs.length];
    TreeSet<Integer> all = new TreeSet<>();
    for (int v : z.vals) {
      all.add(v);
    }
    for (int i = 0; i < xs.length; i++) {
      e[i] = enc(xs[i]);
      for (int v : e[i].vals) {
        all.add(v);
      }
    }
    for (int v : all) {
      int[] c = new int[xs.length + 1];
      if (max) {
        // z >= v iff some x >= v
        c[0] = -z.ge(v);
        for (int i = 0; i < xs.length; i++) {
          add(-e[i].ge(v), z.ge(v));
          c[i + 1] = e[i].ge(v);
        }
      } else {
        // z <= v iff some x <= v
        c[0] = -z.le(v);
        for (int i = 0; i < xs.length; i++) {
          add(-e[i].le(v), z.le(v));
          c[i + 1] = e[i].le(v);
        }
      }
      add(c);
    }
  }

  private void lexLe(Enc[] x, Enc[] y) {
    int e = T;
    for (int i = 0; i < x.length; i++) {
      for (int v : x[i].vals) {
        add(-e, -x[i].ge(v), y[i].ge(v));
      }
      if (i == x.length - 1) {
        break;
      }
      int ne = newVar();
      for (int v : x[i].vals) {
        if (y[i].has(v)) {
          add(-e, -x[i].eq(v), -y[i].eq(v), ne);
        }
      }
      add(-ne, e);
      for (int v : x[i].vals) {
        add(-ne, -x[i].eq(v), y[i].eq(v));
      }
      e = ne;
    }
  }

  private void precede(int[] t, IntVar[] xs) {
    Enc[] e = new Enc[xs.length];
    for (int i = 0; i < xs.length; i++) {
      e[i] = enc(xs[i]);
    }
    for (int k = 0; k + 1 < t.length; k++) {
      int s = t[k];
      int u = t[k + 1];
      int seen = F;
      for (Enc x : e) {
        add(-x.eq(u), seen);
        int ns = newVar();
        int q = x.eq(s);
        add(-seen, ns);
        add(-q, ns);
        add(-ns, seen, q);
        seen = ns;
      }
    }
  }

  private void table(IntVar[] xs, int[] t, int star, boolean shortTable) {
    int k = xs.length;
    Enc[] e = new Enc[k];
    for (int i = 0; i < k; i++) {
      e[i] = enc(xs[i]);
    }
    if (k == 2 && !shortTable) {
      binaryTable(e, t);
      return;
    }
    List<Integer> sel = new ArrayList<>();
    Map<Long, List<Integer>> sup = new HashMap<>();
    List<List<Integer>> starOf = new ArrayList<>();
    for (int i = 0; i < k; i++) {
      starOf.add(new ArrayList<>());
    }
    rows:
    // a table without columns has no rows, so no selector: the empty clause
    for (int r = 0; k > 0 && r + k <= t.length; r += k) {
      for (int i = 0; i < k; i++) {
        int a = t[r + i];
        if (!(shortTable && a == star) && !e[i].has(a)) {
          continue rows;
        }
      }
      int s = newVar();
      sel.add(s);
      for (int i = 0; i < k; i++) {
        int a = t[r + i];
        if (shortTable && a == star) {
          starOf.get(i).add(s);
          continue;
        }
        add(-s, e[i].eq(a));
        sup.computeIfAbsent(((long) i << 32) ^ (a & 0xffffffffL), z -> new ArrayList<>()).add(s);
      }
    }
    add(sel);
    for (int i = 0; i < k; i++) {
      for (int v : e[i].vals) {
        List<Integer> c = new ArrayList<>();
        c.add(-e[i].eq(v));
        c.addAll(sup.getOrDefault(((long) i << 32) ^ (v & 0xffffffffL), List.of()));
        c.addAll(starOf.get(i));
        add(c);
      }
    }
  }

  /**
   * The support encoding of a binary table (Kasif 1990; Gent, ECAI 2002): a value of one column
   * implies one of its supports in the other, so unit propagation keeps arc consistency.
   */
  private void binaryTable(Enc[] e, int[] t) {
    for (int side = 0; side < 2; side++) {
      Enc a = e[side];
      Enc b = e[1 - side];
      Map<Integer, TreeSet<Integer>> sup = new HashMap<>();
      for (int r = 0; r + 2 <= t.length; r += 2) {
        int va = t[r + side];
        int vb = t[r + 1 - side];
        if (a.has(va) && b.has(vb)) {
          sup.computeIfAbsent(va, z -> new TreeSet<>()).add(vb);
        }
      }
      for (int v : a.vals) {
        List<Integer> c = new ArrayList<>();
        c.add(-a.eq(v));
        for (int w : sup.getOrDefault(v, new TreeSet<>())) {
          c.add(b.eq(w));
        }
        add(c);
      }
    }
  }

  private void regular(ASTConstElem n) {
    IntVar[] xs = vars(n, 0);
    int q = integer(n, 1);
    int[] d = ints(n, 3);
    int q0 = integer(n, 4);
    int[] fin = set(n, 5);
    int minIndex = integer(n, 6);
    int cols = d.length / q;
    Enc[] e = new Enc[xs.length];
    for (int i = 0; i < xs.length; i++) {
      e[i] = enc(xs[i]);
      if (e[i].size() > regularDomain) {
        // the CP side handles automata over larger alphabets better (RotatingWorkforce2,
        // NurseRostering)
        throw new NotCompiled("regular over " + e[i].size() + " values");
      }
    }
    int len = xs.length;
    // good[i][state]: the state at position i reaches a final state
    boolean[][] good = new boolean[len + 1][q + 1];
    for (int f : fin) {
      if (f >= 1 && f <= q) {
        good[len][f] = true;
      }
    }
    for (int i = len - 1; i >= 0; i--) {
      for (int s = 1; s <= q; s++) {
        for (int v : e[i].vals) {
          int to = delta(d, cols, s, v, minIndex);
          if (to > 0 && good[i + 1][to]) {
            good[i][s] = true;
            break;
          }
        }
      }
    }
    // node literals, from the last layer back
    int[][] node = new int[len + 1][q + 1];
    for (int s = 1; s <= q; s++) {
      node[len][s] = good[len][s] ? T : F;
    }
    for (int i = len - 1; i >= 0; i--) {
      for (int s = 1; s <= q; s++) {
        if (!good[i][s]) {
          node[i][s] = F;
          continue;
        }
        int[] kids = new int[e[i].size()];
        boolean same = true;
        for (int j = 0; j < kids.length; j++) {
          int to = delta(d, cols, s, e[i].vals[j], minIndex);
          kids[j] = to > 0 ? node[i + 1][to] : F;
          same &= kids[j] == kids[0];
        }
        if (same) {
          node[i][s] = kids[0];
          continue;
        }
        int o = newVar();
        for (int j = 0; j < kids.length; j++) {
          add(-o, -e[i].eq[j], kids[j]);
          add(o, -e[i].eq[j], -kids[j]);
        }
        node[i][s] = o;
      }
    }
    add(q0 >= 1 && q0 <= q ? node[0][q0] : F);
  }

  private static int delta(int[] d, int cols, int s, int v, int minIndex) {
    int j = v - minIndex;
    if (s < 1 || j < 0 || j >= cols) {
      return 0;
    }
    return d[(s - 1) * cols + j];
  }

  // ---------------------------------------------------------------- linear

  private enum Op {
    LE,
    EQ,
    NE
  }

  /**
   * Encodes sum(a * x) op k. With r == 0 the constraint holds; otherwise r implies it (imp) or r
   * holds exactly when it holds.
   */
  private void linear(int[] a, IntVar[] xs, Op op, long k, int r, boolean imp) {
    Map<Enc, Long> merged = new IdentityHashMap<>();
    List<Enc> order = new ArrayList<>();
    for (int i = 0; i < xs.length; i++) {
      if (a[i] == 0) {
        continue;
      }
      Enc e = enc(xs[i]);
      if (e.size() == 1) {
        k -= (long) a[i] * e.lo();
        continue;
      }
      if (!merged.containsKey(e)) {
        order.add(e);
      }
      merged.merge(e, (long) a[i], Long::sum);
    }
    List<long[]> coef = new ArrayList<>();
    List<Enc> terms = new ArrayList<>();
    for (Enc e : order) {
      long c = merged.get(e);
      if (c != 0) {
        coef.add(new long[] {c});
        terms.add(e);
      }
    }
    long[] c = new long[terms.size()];
    for (int i = 0; i < c.length; i++) {
      c[i] = coef.get(i)[0];
    }
    Enc[] t = terms.toArray(new Enc[0]);
    if (r == 0) {
      if (op == Op.NE) {
        add(-relation(c, t, Op.EQ, k));
      } else if (t.length <= 2) {
        small(c, t, op, k, 0);
      } else {
        add(relation(c, t, op, k));
      }
      return;
    }
    int p = op == Op.NE ? -relation(c, t, Op.EQ, k) : relation(c, t, op, k);
    link(p, r, imp);
  }

  // int_lin_{eq,le,ne}[_reif|_imp](a, x, k[, r])
  private void linear(ASTConstElem n) {
    String name = n.getName();
    Op op =
        switch (name.substring(8, 10)) {
          case "eq" -> Op.EQ;
          case "le" -> Op.LE;
          default -> Op.NE;
        };
    boolean plain = name.length() == 10;
    int r = plain ? 0 : lit(var(n, 3));
    linear(ints(n, 0), vars(n, 1), op, integer(n, 2), r, name.endsWith("_imp"));
  }

  private static long lo(long a, Enc e) {
    return a > 0 ? a * e.lo() : a * e.hi();
  }

  private static long hi(long a, Enc e) {
    return a > 0 ? a * e.hi() : a * e.lo();
  }

  // 1-2 terms, as clauses that hold or that a literal p implies (clauses get -p)
  private void small(long[] a, Enc[] t, Op op, long k, int p) {
    if (p == 0) {
      // a constraint that holds: its clauses without a literal
      p = T;
    }
    if (op == Op.EQ) {
      small(a, t, Op.LE, k, p);
      long[] neg = new long[a.length];
      for (int i = 0; i < a.length; i++) {
        neg[i] = -a[i];
      }
      small(neg, t, Op.LE, -k, p);
      return;
    }
    if (t.length == 0) {
      add(-p, 0 <= k ? T : F);
      return;
    }
    if (t.length == 1) {
      add(-p, bound(a[0], t[0], k));
      return;
    }
    Enc x = t[0];
    for (int v : x.vals) {
      // a > 0: x >= v implies b*y <= k - a*v; a < 0: x <= v implies it
      int premise = a[0] > 0 ? x.ge(v) : x.le(v);
      add(-p, -premise, bound(a[1], t[1], k - a[0] * v));
    }
  }

  // the literal of b * y <= c
  private static int bound(long b, Enc y, long c) {
    if (b > 0) {
      long q = Math.floorDiv(c, b);
      return q >= y.hi() ? T : q < y.lo() ? F : y.le((int) q);
    }
    // b < 0: b * y <= c iff y >= ceil(c / b) = -floor(c / -b)
    long ceil = -Math.floorDiv(c, -b);
    return ceil <= y.lo() ? T : ceil > y.hi() ? F : y.ge((int) ceil);
  }

  // a literal that holds exactly when sum(a * x) op k (op LE or EQ)
  private int relation(long[] a, Enc[] t, Op op, long k) {
    if (t.length == 0) {
      return (op == Op.LE ? 0 <= k : k == 0) ? T : F;
    }
    long lo = 0;
    long hi = 0;
    for (int i = 0; i < t.length; i++) {
      lo += lo(a[i], t[i]);
      hi += hi(a[i], t[i]);
    }
    if (op == Op.LE && hi <= k) {
      return T;
    }
    if (op == Op.LE && lo > k || op == Op.EQ && (k < lo || k > hi)) {
      return F;
    }
    if (t.length <= 2) {
      int p = newVar();
      small(a, t, op, k, p);
      if (op == Op.LE) {
        long[] neg = new long[a.length];
        for (int i = 0; i < a.length; i++) {
          neg[i] = -a[i];
        }
        small(neg, t, Op.LE, -k - 1, -p);
      } else if (t.length == 1) {
        if (k % a[0] == 0) {
          long v = k / a[0];
          add(p, v == (int) v ? -t[0].eq((int) v) : T);
        }
      } else {
        for (int v : t[0].vals) {
          long rest = k - a[0] * v;
          if (rest % a[1] == 0 && rest / a[1] == (int) (rest / a[1])) {
            add(p, -t[0].eq(v), -t[1].eq((int) (rest / a[1])));
          }
        }
      }
      return p;
    }
    return diagram(a, t, op, k);
  }

  // a decision diagram over the partial sums, or adders when it would be too large
  private int diagram(long[] a0, Enc[] t0, Op op, long k) {
    int n = t0.length;
    Integer[] idx = new Integer[n];
    for (int i = 0; i < n; i++) {
      idx[i] = i;
    }
    Arrays.sort(idx, (p, q) -> Integer.compare(t0[p].size(), t0[q].size()));
    long[] a = new long[n];
    Enc[] t = new Enc[n];
    for (int i = 0; i < n; i++) {
      a[i] = a0[idx[i]];
      t[i] = t0[idx[i]];
    }
    long[] mins = new long[n + 1];
    long[] maxs = new long[n + 1];
    for (int i = n - 1; i >= 0; i--) {
      mins[i] = mins[i + 1] + lo(a[i], t[i]);
      maxs[i] = maxs[i + 1] + hi(a[i], t[i]);
    }
    long g = 0;
    for (long x : a) {
      g = gcd(g, Math.abs(x));
    }
    // forward: the partial sums that are not decided yet, per layer
    List<long[]> layers = new ArrayList<>();
    layers.add(new long[] {0});
    long states = 1;
    for (int i = 0; i < n; i++) {
      TreeSet<Long> next = new TreeSet<>();
      for (long s : layers.get(i)) {
        if (decided(s, i, op, k, mins, maxs, g) != 0) {
          continue;
        }
        for (int v : t[i].vals) {
          long ns = s + a[i] * v;
          if (decided(ns, i + 1, op, k, mins, maxs, g) == 0) {
            next.add(ns);
          }
        }
      }
      states += next.size();
      if (states > mddNodes) {
        return adders(a, t, op, k);
      }
      layers.add(next.stream().mapToLong(Long::longValue).toArray());
    }
    mdds++;
    // backward: a literal per undecided state
    Map<Long, Integer> below = new HashMap<>();
    for (int i = n - 1; i >= 0; i--) {
      Map<Long, Integer> here = new HashMap<>();
      for (long s : layers.get(i)) {
        if (decided(s, i, op, k, mins, maxs, g) != 0) {
          continue;
        }
        int[] kids = new int[t[i].size()];
        boolean same = true;
        for (int j = 0; j < kids.length; j++) {
          long ns = s + a[i] * t[i].vals[j];
          int dd = decided(ns, i + 1, op, k, mins, maxs, g);
          kids[j] = dd != 0 ? dd : below.get(ns);
          same &= kids[j] == kids[0];
        }
        if (same) {
          here.put(s, kids[0]);
          continue;
        }
        int o = newVar();
        for (int j = 0; j < kids.length; j++) {
          add(-o, -t[i].eq[j], kids[j]);
          add(o, -t[i].eq[j], -kids[j]);
        }
        here.put(s, o);
      }
      below = here;
    }
    int root = decided(0, 0, op, k, mins, maxs, g);
    return root != 0 ? root : below.get(0L);
  }

  // T or F when the partial sum s before layer i decides the relation, 0 otherwise
  private static int decided(long s, int i, Op op, long k, long[] mins, long[] maxs, long g) {
    if (op == Op.LE) {
      if (s + mins[i] > k) {
        return F;
      }
      if (s + maxs[i] <= k) {
        return T;
      }
      return 0;
    }
    if (k < s + mins[i] || k > s + maxs[i]) {
      return F;
    }
    if (i == mins.length - 1) {
      return s == k ? T : F;
    }
    if (g > 1 && Math.floorMod(k - s, g) != 0) {
      return F;
    }
    return 0;
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long r = a % b;
      a = b;
      b = r;
    }
    return a;
  }

  // the log encoding: the positive and the negative terms as binary numbers, compared
  private int adders(long[] a, Enc[] t, Op op, long k) {
    logs++;
    Map<Integer, List<Integer>> pos = new HashMap<>();
    Map<Integer, List<Integer>> neg = new HashMap<>();
    long kk = k;
    for (int i = 0; i < t.length; i++) {
      Enc v = t[i];
      kk -= a[i] * v.lo();
      Map<Integer, List<Integer>> side = a[i] > 0 ? pos : neg;
      long span = (long) v.hi() - v.lo();
      int nb = 64 - Long.numberOfLeadingZeros(span);
      long aa = Math.abs(a[i]);
      for (int j = 0; j < nb; j++) {
        List<Integer> in = new ArrayList<>();
        for (int q = 0; q < v.size(); q++) {
          if ((((long) v.vals[q] - v.lo()) >> j & 1) == 1) {
            in.add(v.eq[q]);
          }
        }
        int bit = or(in.stream().mapToInt(Integer::intValue).toArray());
        for (int b = 0; b < 63; b++) {
          if ((aa >> b & 1) == 1) {
            side.computeIfAbsent(j + b, z -> new ArrayList<>()).add(bit);
          }
        }
      }
    }
    Map<Integer, List<Integer>> constSide = kk >= 0 ? neg : pos;
    long ck = Math.abs(kk);
    for (int b = 0; b < 63; b++) {
      if ((ck >> b & 1) == 1) {
        constSide.computeIfAbsent(b, z -> new ArrayList<>()).add(T);
      }
    }
    List<Integer> p = reduce(pos);
    List<Integer> q = reduce(neg);
    int w = Math.max(p.size(), q.size());
    while (p.size() < w) {
      p.add(F);
    }
    while (q.size() < w) {
      q.add(F);
    }
    if (op == Op.EQ) {
      int[] eqs = new int[w];
      for (int i = 0; i < w; i++) {
        eqs[i] = equalLit(p.get(i), q.get(i));
      }
      return and(eqs);
    }
    // p <= q, from the least significant bit up
    int le = T;
    for (int i = 0; i < w; i++) {
      int x = p.get(i);
      int y = q.get(i);
      le = or(and(-x, y), and(equalLit(x, y), le));
    }
    return le;
  }

  private List<Integer> reduce(Map<Integer, List<Integer>> cols) {
    Map<Integer, List<Integer>> c = new HashMap<>();
    int top = -1;
    for (Map.Entry<Integer, List<Integer>> e : cols.entrySet()) {
      c.put(e.getKey(), new ArrayList<>(e.getValue()));
      top = Math.max(top, e.getKey());
    }
    List<Integer> out = new ArrayList<>();
    for (int w = 0; w <= top; w++) {
      List<Integer> col = new ArrayList<>();
      for (int x : c.getOrDefault(w, List.of())) {
        if (x != F) {
          col.add(x);
        }
      }
      while (col.size() >= 3) {
        int x = col.remove(col.size() - 1);
        int y = col.remove(col.size() - 1);
        int z = col.remove(col.size() - 1);
        col.add(0, xor3(x, y, z));
        c.computeIfAbsent(w + 1, v -> new ArrayList<>()).add(maj(x, y, z));
        top = Math.max(top, w + 1);
      }
      if (col.size() == 2) {
        int x = col.get(0);
        int y = col.get(1);
        int s = xor3(x, y, F);
        c.computeIfAbsent(w + 1, v -> new ArrayList<>()).add(and(x, y));
        top = Math.max(top, w + 1);
        col.clear();
        col.add(s);
      }
      out.add(col.isEmpty() ? F : col.get(0));
    }
    return out;
  }
}
