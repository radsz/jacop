/*
 * DecompositionCheck.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.decomposition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.jacop.decomposition.FznBuilder.Term;
import org.jacop.decomposition.FznModel.Expr;
import org.jacop.decomposition.FznModel.SetLit;

/**
 * Decompositions of the JaCoP globals that have no MiniZinc standard decomposition, or whose
 * MiniZinc global JaCoP's library maps to a JaCoP-only predicate. Each is written from the
 * definition of the predicate in JaCoP's library ({@code jacop-flatzinc/src/main/minizinc}) with
 * FlatZinc built-ins only, so that {@link AllSolutionsSuite} and {@link DecompositionCheck} can
 * compare the propagator with it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class JacopDecompositions {

  private JacopDecompositions() {}

  private static long[] ones(int n) {
    long[] c = new long[n];
    Arrays.fill(c, 1);
    return c;
  }

  private static Term count(FznBuilder b, List<Term> x, Term y) {
    return StdDecompositions.countValue(b, x, y);
  }

  /** jacop_count_var_reif(x, y, c, b): b <-> count(x, y) = c. */
  static void countVarReif(FznBuilder b, List<Expr> a) {
    Term n = count(b, b.array(a.get(0)), b.term(a.get(1)));
    b.boolEq(
        b.linearReif(new long[] {1, -1}, List.of(n, b.term(a.get(2))), "eq", 0), b.term(a.get(3)));
  }

  /** jacop_count_var_le(x, y, c, k): count(x, y) + k <= c. */
  static void countVarLe(FznBuilder b, List<Expr> a) {
    Term n = count(b, b.array(a.get(0)), b.term(a.get(1)));
    b.linear(new long[] {1, -1}, List.of(n, b.term(a.get(2))), "le", -b.intArg(a.get(3)));
  }

  /** jacop_count_var_ge(x, y, c, k): c + k <= count(x, y). */
  static void countVarGe(FznBuilder b, List<Expr> a) {
    Term n = count(b, b.array(a.get(0)), b.term(a.get(1)));
    b.linear(new long[] {1, -1}, List.of(b.term(a.get(2)), n), "le", -b.intArg(a.get(3)));
  }

  /** jacop_atleast_reif(x, v, n, b): b <-> count(x, v) >= n. */
  static void atLeastReif(FznBuilder b, List<Expr> a) {
    Term n = count(b, b.array(a.get(0)), b.term(a.get(1)));
    b.boolEq(
        b.linearReif(new long[] {-1}, List.of(n), "le", -b.intArg(a.get(2))), b.term(a.get(3)));
  }

  private static Term memberTerm(FznBuilder b, List<Expr> a) {
    Term y = b.term(a.get(1));
    List<Term> eqs = new ArrayList<>();
    for (Term xi : b.array(a.get(0))) {
      eqs.add(b.eqReif(xi, y));
    }
    return b.or(eqs);
  }

  /** jacop_member_bool(x, y): exists (i) (x[i] = y). */
  static void memberBool(FznBuilder b, List<Expr> a) {
    b.require(memberTerm(b, a));
  }

  /** jacop_member_bool_reif(x, y, b): b <-> exists (i) (x[i] = y). */
  static void memberBoolReif(FznBuilder b, List<Expr> a) {
    b.boolEq(memberTerm(b, a), b.term(a.get(2)));
  }

  /** A tuple matches: the conjunction of x[j] = t[j] over the entries that are not {@code star}. */
  private static Term row(FznBuilder b, List<Term> x, List<Expr> flat, int r, Long star) {
    List<Term> eqs = new ArrayList<>();
    for (int j = 0; j < x.size(); j++) {
      Term t = b.term(flat.get(r * x.size() + j));
      if (star != null && t.isConst() && t.value() == star) {
        continue;
      }
      eqs.add(b.eqReif(x.get(j), t));
    }
    return b.and(eqs);
  }

  private static Term inTable(FznBuilder b, List<Term> x, Expr table, Long star) {
    List<Expr> flat = b.model.elements(table);
    List<Term> rows = new ArrayList<>();
    for (int r = 0; x.size() > 0 && r < flat.size() / x.size(); r++) {
      rows.add(row(b, x, flat, r, star));
    }
    return b.or(rows);
  }

  /** jacop_short_table_int(x, t, star): some row matches, {@code star} matches any value. */
  static void shortTable(FznBuilder b, List<Expr> a) {
    b.require(inTable(b, b.array(a.get(0)), a.get(1), b.intArg(a.get(2))));
  }

  /** jacop_negative_table_int(x, t): no row matches. */
  static void negativeTable(FznBuilder b, List<Expr> a) {
    b.require(b.not(inTable(b, b.array(a.get(0)), a.get(1), null)));
  }

  /** jacop_table_*_reif(x, t, b): b <-> some row matches. */
  static void tableReif(FznBuilder b, List<Expr> a) {
    b.boolEq(inTable(b, b.array(a.get(0)), a.get(1), null), b.term(a.get(2)));
  }

  /** jacop_table_*_imp(x, t, b): b -> some row matches. */
  static void tableImp(FznBuilder b, List<Expr> a) {
    b.clause(List.of(inTable(b, b.array(a.get(0)), a.get(1), null)), List.of(b.term(a.get(2))));
  }

  /** jacop_among_var(x, v, n): n = sum (i) (exists (j) (x[i] = v[j])). */
  static void amongVar(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    List<Term> v = b.array(a.get(1));
    List<Term> terms = new ArrayList<>();
    for (Term xi : x) {
      List<Term> eqs = new ArrayList<>();
      for (Term vj : v) {
        eqs.add(b.eqReif(xi, vj));
      }
      terms.add(b.bool2int(b.or(eqs)));
    }
    terms.add(b.term(a.get(2)));
    long[] c = ones(terms.size());
    c[x.size()] = -1;
    b.linear(c, terms, "eq", 0);
  }

  /** jacop_channel(x, b, values): b[k] <-> x = the k-th smallest value of {@code values}. */
  static void channel(FznBuilder b, List<Expr> a) {
    Term x = b.term(a.get(0));
    List<Term> bs = b.array(a.get(1));
    long[] values = b.model.set(a.get(2)).values();
    for (int k = 0; k < bs.size(); k++) {
      Term eq = k < values.length ? b.eqReif(x, FznBuilder.constant(values[k])) : FznBuilder.FALSE;
      b.boolEq(eq, bs.get(k));
    }
  }

  /** jacop_sequence(x, values, q, min, max): every q consecutive x have min..max in values. */
  static void sequence(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    SetLit values = b.model.set(a.get(1));
    int q = (int) b.intArg(a.get(2));
    long min = b.intArg(a.get(3));
    long max = b.intArg(a.get(4));
    List<Term> in = new ArrayList<>();
    for (Term xi : x) {
      in.add(b.bool2int(b.inReif(xi, values)));
    }
    for (int i = 0; i + q <= x.size(); i++) {
      List<Term> window = in.subList(i, i + q);
      b.linear(ones(q), window, "le", max);
      long[] neg = ones(q);
      Arrays.fill(neg, -1);
      b.linear(neg, window, "le", -min);
    }
  }

  /** x[i] + p <= x[j] \/ x[j] + p <= x[i] for every i < j. */
  static void interDistance(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    long p = b.intArg(a.get(1));
    for (int i = 0; i < x.size(); i++) {
      for (int j = i + 1; j < x.size(); j++) {
        Term ij = b.linearReif(new long[] {1, -1}, List.of(x.get(i), x.get(j)), "le", -p);
        Term ji = b.linearReif(new long[] {1, -1}, List.of(x.get(j), x.get(i)), "le", -p);
        b.clause(List.of(ij, ji), List.of());
      }
    }
  }

  /** For every v, at most m of the x take a value in v..v+p-1. */
  static void multiInterDistance(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    long m = b.intArg(a.get(1));
    long p = b.intArg(a.get(2));
    long lo = Long.MAX_VALUE;
    long hi = Long.MIN_VALUE;
    for (Term xi : x) {
      lo = Math.min(lo, b.lb(xi));
      hi = Math.max(hi, b.ub(xi));
    }
    for (long v = lo; v <= hi; v++) {
      List<Term> in = new ArrayList<>();
      for (Term xi : x) {
        in.add(b.bool2int(b.inReif(xi, SetLit.range(v, v + p - 1))));
      }
      b.linear(ones(in.size()), in, "le", m);
    }
  }

  private static Term abs(FznBuilder b, Term t) {
    long lo = b.lb(t);
    long hi = b.ub(t);
    Term r = b.newInt(lo >= 0 ? lo : hi <= 0 ? -hi : 0, Math.max(Math.abs(lo), Math.abs(hi)));
    b.post("int_abs", t, r);
    return r;
  }

  /** jacop_deviation(x, a, b, s, d): sum(x) = s, d = sum (i) |a * x[i] - b|. */
  static void deviation(FznBuilder b, List<Expr> a) {
    deviationOrSpread(b, a, false);
  }

  /** jacop_spread(x, a, b, s, d): sum(x) = s, d = sum (i) (a * x[i] - b)^2. */
  static void spread(FznBuilder b, List<Expr> a) {
    deviationOrSpread(b, a, true);
  }

  private static void deviationOrSpread(FznBuilder b, List<Expr> a, boolean square) {
    List<Term> x = b.array(a.get(0));
    long ca = b.intArg(a.get(1));
    long cb = b.intArg(a.get(2));
    long s = b.intArg(a.get(3));
    b.linear(ones(x.size()), x, "eq", s);
    List<Term> terms = new ArrayList<>();
    for (Term xi : x) {
      Term t = b.sum(new long[] {ca}, List.of(xi), -cb);
      terms.add(square ? b.times(t, t) : abs(b, t));
    }
    terms.add(b.term(a.get(4)));
    long[] c = ones(terms.size());
    c[x.size()] = -1;
    b.linear(c, terms, "eq", 0);
  }

  /** jacop_diff2(r): r is [x, y, lx, ly] per rectangle, as jacop_list_diff2. */
  static void diff2(FznBuilder b, List<Expr> a) {
    List<Expr> r = b.model.elements(a.get(0));
    List<Expr> x = new ArrayList<>();
    List<Expr> y = new ArrayList<>();
    List<Expr> lx = new ArrayList<>();
    List<Expr> ly = new ArrayList<>();
    for (int i = 0; i + 3 < r.size(); i += 4) {
      x.add(r.get(i));
      y.add(r.get(i + 1));
      lx.add(r.get(i + 2));
      ly.add(r.get(i + 3));
    }
    StdDecompositions.diffnNonstrict(
        b,
        List.of(
            new FznModel.ArrayLit(x),
            new FznModel.ArrayLit(y),
            new FznModel.ArrayLit(lx),
            new FznModel.ArrayLit(ly)));
  }

  /**
   * jacop_diffn_k(posn, size, k, strict): box i occupies posn[i * k + d] .. posn[i * k + d] +
   * size[i * k + d] in dimension d; two boxes are apart in some dimension (fzn_diffn_k), or under
   * strict = false one of them has a zero size somewhere (fzn_diffn_nonstrict_k).
   */
  static void diffnK(FznBuilder b, List<Expr> a) {
    List<Term> p = b.array(a.get(0));
    List<Term> l = b.array(a.get(1));
    int k = (int) b.intArg(a.get(2));
    boolean strict = b.term(a.get(3)).isTrue();
    int n = p.size() / k;
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        List<Term> or = new ArrayList<>();
        for (int d = 0; d < k; d++) {
          Term pi = p.get(i * k + d);
          Term li = l.get(i * k + d);
          Term pj = p.get(j * k + d);
          Term lj = l.get(j * k + d);
          if (!strict) {
            or.add(b.eqReif(li, FznBuilder.constant(0)));
            or.add(b.eqReif(lj, FznBuilder.constant(0)));
          }
          or.add(b.linearReif(new long[] {1, 1, -1}, List.of(pi, li, pj), "le", 0));
          or.add(b.linearReif(new long[] {1, 1, -1}, List.of(pj, lj, pi), "le", 0));
        }
        b.clause(or, List.of());
      }
    }
  }

  /** jacop_sort(x, y): y is x sorted, through a permutation as fzn_sort does. */
  static void sort(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    List<Term> y = b.array(a.get(1));
    int n = x.size();
    List<Term> z = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      z.add(b.newInt(1, n));
    }
    sortWith(b, x, y, z, 1);
    // z is not an argument: make it the stable permutation so that every (x, y) has exactly one z
    // and the decomposition prints each solution once (equal x keep their order in y)
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        b.clause(List.of(b.neReif(x.get(i), x.get(j)), b.ltReif(z.get(i), z.get(j))), List.of());
      }
    }
  }

  /** jacop_sort_permutation(x, y, z, offset): y is x sorted and x[i] = y[z[i] - offset]. */
  static void sortPermutation(FznBuilder b, List<Expr> a) {
    sortWith(b, b.array(a.get(0)), b.array(a.get(1)), b.array(a.get(2)), b.intArg(a.get(3)));
  }

  private static void sortWith(FznBuilder b, List<Term> x, List<Term> y, List<Term> z, long off) {
    int n = x.size();
    if (y.size() != n || z.size() != n) {
      b.fail();
      return;
    }
    StdDecompositions.allDifferent(b, z);
    for (int i = 0; i < n; i++) {
      // z[i] in off..off+n-1 and x[i] = y[z[i] - off + 1] (array_var_int_element is 1-based)
      b.linear(new long[] {1}, List.of(z.get(i)), "le", off + n - 1);
      b.linear(new long[] {-1}, List.of(z.get(i)), "le", -off);
      Term index = b.sum(new long[] {1}, List.of(z.get(i)), 1 - off);
      b.post("array_var_int_element", index, y, x.get(i));
    }
    StdDecompositions.increasing(b, y, false, false);
  }

  /** jacop_alldifferent_opt(x, occurs): x[i] != x[j] whenever both occur. */
  static void allDifferentOpt(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    List<Term> o = b.array(a.get(1));
    for (int i = 0; i < x.size(); i++) {
      for (int j = i + 1; j < x.size(); j++) {
        b.clause(List.of(b.neReif(x.get(i), x.get(j))), List.of(o.get(i), o.get(j)));
      }
    }
  }

  /**
   * jacop_softalldiff(x, d, useDec): with useDec d is the number of pairs i < j with x[i] = x[j],
   * otherwise length(x) minus the number of different values.
   */
  static void softAllDifferent(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    Term d = b.term(a.get(1));
    boolean useDec = b.intArg(a.get(2)) != 0;
    List<Term> terms = new ArrayList<>();
    if (useDec) {
      for (int i = 0; i < x.size(); i++) {
        for (int j = i + 1; j < x.size(); j++) {
          terms.add(b.bool2int(b.eqReif(x.get(i), x.get(j))));
        }
      }
      terms.add(d);
      long[] c = ones(terms.size());
      c[terms.size() - 1] = -1;
      b.linear(c, terms, "eq", 0);
    } else {
      long lo = Long.MAX_VALUE;
      long hi = Long.MIN_VALUE;
      for (Term xi : x) {
        lo = Math.min(lo, b.lb(xi));
        hi = Math.max(hi, b.ub(xi));
      }
      for (long v = lo; v <= hi; v++) {
        List<Term> eqs = new ArrayList<>();
        for (Term xi : x) {
          eqs.add(b.eqReif(xi, FznBuilder.constant(v)));
        }
        terms.add(b.bool2int(b.or(eqs)));
      }
      // d + nvalue = length(x)
      terms.add(d);
      b.linear(ones(terms.size()), terms, "eq", x.size());
    }
  }

  /**
   * jacop_softgcc(x, values, hard, soft, cost): hard[i] = count(x, values[i]) and cost = sum (i)
   * |hard[i] - soft[i]|.
   */
  static void softGcc(FznBuilder b, List<Expr> a) {
    softGcc(b, a, false);
  }

  /** jacop_softgcc_var: as jacop_softgcc with cost = max(shortage, excess). */
  static void softGccVar(FznBuilder b, List<Expr> a) {
    softGcc(b, a, true);
  }

  private static void softGcc(FznBuilder b, List<Expr> a, boolean variableBased) {
    List<Term> x = b.array(a.get(0));
    long[] values = b.intArray(a.get(1));
    List<Term> hard = b.array(a.get(2));
    List<Term> soft = b.array(a.get(3));
    Term cost = b.term(a.get(4));
    List<Term> diffs = new ArrayList<>();
    List<Term> shortage = new ArrayList<>();
    List<Term> excess = new ArrayList<>();
    for (int i = 0; i < values.length; i++) {
      b.eq(count(b, x, FznBuilder.constant(values[i])), hard.get(i));
      Term diff = b.sum(new long[] {1, -1}, List.of(hard.get(i), soft.get(i)), 0);
      diffs.add(abs(b, diff));
      shortage.add(maxZero(b, b.sum(new long[] {-1}, List.of(diff), 0)));
      excess.add(maxZero(b, diff));
    }
    if (variableBased) {
      // the variable based measure requires sum(soft_counters) <= length(x), which SoftGCC imposes
      b.linear(ones(soft.size()), soft, "le", x.size());
      Term s = b.sum(ones(shortage.size()), shortage, 0);
      Term e = b.sum(ones(excess.size()), excess, 0);
      b.post("int_max", s, e, cost);
    } else {
      diffs.add(cost);
      long[] c = ones(diffs.size());
      c[diffs.size() - 1] = -1;
      b.linear(c, diffs, "eq", 0);
    }
  }

  private static Term maxZero(FznBuilder b, Term t) {
    Term r = b.newInt(Math.max(0, b.lb(t)), Math.max(0, b.ub(t)));
    b.post("int_max", t, FznBuilder.constant(0), r);
    return r;
  }

  /**
   * jacop_reservoir(times, changes, min, max): for every event j, the sum of the changes of the
   * events at or before times[j] is within min..max.
   */
  static void reservoir(FznBuilder b, List<Expr> a) {
    List<Term> t = b.array(a.get(0));
    long[] c = b.intArray(a.get(1));
    long min = b.intArg(a.get(2));
    long max = b.intArg(a.get(3));
    for (int j = 0; j < t.size(); j++) {
      List<Term> terms = new ArrayList<>();
      long[] coefs = new long[t.size()];
      for (int i = 0; i < t.size(); i++) {
        terms.add(i == j ? FznBuilder.constant(1) : b.bool2int(b.leReif(t.get(i), t.get(j))));
        coefs[i] = c[i];
      }
      Term level = b.sum(coefs, terms, 0);
      b.linear(new long[] {1}, List.of(level), "le", max);
      b.linear(new long[] {-1}, List.of(level), "le", -min);
    }
  }

  /**
   * jacop_stocking_cost(x, d, h, cost, c): x[i] <= d[i], at most c of the x per period, and cost =
   * sum (i) h[i] * (d[i] - x[i]).
   */
  static void stockingCost(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    long[] d = b.intArray(a.get(1));
    long[] h = b.intArray(a.get(2));
    Term cost = b.term(a.get(3));
    long cap = b.intArg(a.get(4));
    long lo = Long.MAX_VALUE;
    long hi = Long.MIN_VALUE;
    long total = 0;
    for (int i = 0; i < x.size(); i++) {
      b.linear(new long[] {1}, List.of(x.get(i)), "le", d[i]);
      lo = Math.min(lo, b.lb(x.get(i)));
      hi = Math.max(hi, b.ub(x.get(i)));
      total += h[i] * d[i];
    }
    for (long v = lo; v <= hi; v++) {
      Term n = count(b, x, FznBuilder.constant(v));
      b.linear(new long[] {1}, List.of(n), "le", cap);
    }
    // sum (h[i] * x[i]) + cost = sum (h[i] * d[i])
    List<Term> terms = new ArrayList<>(x);
    terms.add(cost);
    long[] coefs = Arrays.copyOf(h, x.size() + 1);
    coefs[x.size()] = 1;
    b.linear(coefs, terms, "eq", total);
  }

  /** jacop_subcircuit_cost(x, d, cost): subcircuit(x), cost = sum (i) d[i, x[i]]. */
  static void subcircuitCost(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    long[] d = b.intArray(a.get(1));
    int n = x.size();
    StdDecompositions.subcircuit(b, x);
    List<Term> terms = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      long[] row = Arrays.copyOfRange(d, i * n, (i + 1) * n);
      long lo = Arrays.stream(row).min().orElse(0);
      long hi = Arrays.stream(row).max().orElse(0);
      Term c = b.newInt(lo, hi);
      b.post("array_int_element", x.get(i), row, c);
      terms.add(c);
    }
    terms.add(b.term(a.get(2)));
    long[] c = ones(terms.size());
    c[n] = -1;
    b.linear(c, terms, "eq", 0);
  }

  /**
   * jacop_disjunctive_setup(s, d, f, t): t is the square transition matrix flattened row by row, f
   * the 0-based families; s[i] + d[i] + t[f[i], f[j]] <= s[j] or the other way round.
   */
  static void disjunctiveSetup(FznBuilder b, List<Expr> a) {
    List<Term> s = b.array(a.get(0));
    List<Term> d = b.array(a.get(1));
    disjunctiveSetup(b, s, d, b.intArray(a.get(2)), b.intArray(a.get(3)), null);
  }

  /** jacop_disjunctive_setup_optional(s, d, f, t, o): only between tasks that both occur. */
  static void disjunctiveSetupOptional(FznBuilder b, List<Expr> a) {
    List<Term> s = b.array(a.get(0));
    List<Term> d = b.array(a.get(1));
    disjunctiveSetup(b, s, d, b.intArray(a.get(2)), b.intArray(a.get(3)), b.array(a.get(4)));
  }

  private static void disjunctiveSetup(
      FznBuilder b, List<Term> s, List<Term> d, long[] f, long[] t, List<Term> o) {
    int families = (int) Math.round(Math.sqrt(t.length));
    for (Term di : d) {
      b.linear(new long[] {-1}, List.of(di), "le", 0);
    }
    for (int i = 0; i < s.size(); i++) {
      for (int j = i + 1; j < s.size(); j++) {
        long tij = t[(int) (f[i] * families + f[j])];
        long tji = t[(int) (f[j] * families + f[i])];
        Term ij =
            b.linearReif(new long[] {1, 1, -1}, List.of(s.get(i), d.get(i), s.get(j)), "le", -tij);
        Term ji =
            b.linearReif(new long[] {1, 1, -1}, List.of(s.get(j), d.get(j), s.get(i)), "le", -tji);
        b.clause(List.of(ij, ji), o == null ? List.of() : List.of(o.get(i), o.get(j)));
      }
    }
  }

  /** jacop_sum_set(values, weights, selected, total): total = sum of the weights selected. */
  static void sumSet(FznBuilder b, List<Expr> a) {
    long[] values = b.intArray(a.get(0));
    long[] weights = b.intArray(a.get(1));
    String set = b.set(a.get(2));
    List<Term> terms = new ArrayList<>();
    for (long v : values) {
      Term in = b.newBool();
      b.post("set_in_reif", v, set, in);
      terms.add(b.bool2int(in));
    }
    terms.add(b.term(a.get(3)));
    long[] c = Arrays.copyOf(weights, terms.size());
    c[values.length] = -1;
    b.linear(c, terms, "eq", 0);
  }

  /**
   * jacop_stretch(values, min, max, x): x takes only these values, and every maximal run of
   * values[k] is min[k]..max[k] long.
   */
  static void stretch(FznBuilder b, List<Expr> a) {
    long[] values = b.intArray(a.get(0));
    long[] min = b.intArray(a.get(1));
    long[] max = b.intArray(a.get(2));
    List<Term> x = b.array(a.get(3));
    int n = x.size();
    for (Term xi : x) {
      b.in(xi, SetLit.of(Arrays.stream(values).sorted().distinct().toArray()));
    }
    for (int k = 0; k < values.length; k++) {
      Term v = FznBuilder.constant(values[k]);
      List<Term> eq = new ArrayList<>();
      for (Term xi : x) {
        eq.add(b.eqReif(xi, v));
      }
      for (int i = 0; i < n; i++) {
        // a run of values[k] starts at i
        Term start = i == 0 ? eq.get(0) : b.and(List.of(eq.get(i), b.not(eq.get(i - 1))));
        if (i + min[k] - 1 >= n) {
          b.clause(List.of(), List.of(start));
          continue;
        }
        for (int j = i; j <= i + min[k] - 1; j++) {
          b.clause(List.of(eq.get(j)), List.of(start));
        }
        if (i + max[k] < n) {
          List<Term> ends = new ArrayList<>();
          for (int j = i; j <= i + max[k]; j++) {
            ends.add(b.not(eq.get(j)));
          }
          b.clause(ends, List.of(start));
        }
      }
    }
  }
}
