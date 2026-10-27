/*
 * StdDecompositions.java
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import org.jacop.decomposition.FznBuilder.Term;
import org.jacop.decomposition.FznModel.Expr;
import org.jacop.decomposition.FznModel.SetLit;

/**
 * Decompositions of JaCoP's FlatZinc globals into FlatZinc built-ins, following the default
 * decompositions of the MiniZinc 2.10.1 standard library ({@code share/minizinc/std/fzn_*.mzn}).
 * Each entry maps a {@code jacop_*} constraint back to the MiniZinc global that JaCoP's library
 * ({@code jacop-flatzinc/src/main/minizinc}) rewrites into it, and posts what the MiniZinc compiler
 * would post for that global without JaCoP's library. Globals that a standard decomposition calls
 * (such as {@code count} inside {@code at_least}) are decomposed too, so a decomposed model uses
 * built-ins only.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class StdDecompositions {

  /** Posts the decomposition of one constraint. */
  @FunctionalInterface
  interface Decomposer {
    void decompose(FznBuilder b, List<Expr> args);
  }

  private static final Map<String, Decomposer> DECOMPOSERS = new LinkedHashMap<>();

  static {
    DECOMPOSERS.put("jacop_alldiff", (b, a) -> allDifferent(b, b.array(a.get(0))));
    DECOMPOSERS.put("jacop_alldistinct", (b, a) -> allDifferent(b, b.array(a.get(0))));
    DECOMPOSERS.put(
        "jacop_alldifferent_except_0",
        (b, a) -> allDifferentExcept(b, b.array(a.get(0)), SetLit.range(0, 0)));
    DECOMPOSERS.put(
        "jacop_alldifferent_except",
        (b, a) -> allDifferentExcept(b, b.array(a.get(0)), b.model.set(a.get(1))));
    DECOMPOSERS.put("jacop_all_equal_int", (b, a) -> allEqual(b, b.array(a.get(0))));
    DECOMPOSERS.put(
        "jacop_count",
        (b, a) -> b.linear(new long[] {1, -1}, List.of(count(b, a), b.term(a.get(2))), "eq", 0));
    DECOMPOSERS.put(
        "jacop_count_var",
        (b, a) -> b.linear(new long[] {1, -1}, List.of(count(b, a), b.term(a.get(2))), "eq", 0));
    DECOMPOSERS.put(
        "jacop_count_reif",
        (b, a) ->
            b.boolEq(
                b.linearReif(new long[] {1, -1}, List.of(count(b, a), b.term(a.get(2))), "eq", 0),
                b.term(a.get(3))));
    // at_least(n, x, v): count(x, v) >= n
    DECOMPOSERS.put(
        "jacop_atleast",
        (b, a) -> b.linear(new long[] {-1}, List.of(count(b, a)), "le", -b.intArg(a.get(2))));
    // at_most(n, x, v): count(x, v) <= n
    DECOMPOSERS.put(
        "jacop_atmost",
        (b, a) -> b.linear(new long[] {1}, List.of(count(b, a)), "le", b.intArg(a.get(2))));
    DECOMPOSERS.put(
        "jacop_atmost_reif",
        (b, a) ->
            b.boolEq(
                b.linearReif(new long[] {1}, List.of(count(b, a)), "le", b.intArg(a.get(2))),
                b.term(a.get(3))));
    DECOMPOSERS.put("jacop_among", StdDecompositions::among);
    DECOMPOSERS.put("jacop_count_values", StdDecompositions::globalCardinality);
    DECOMPOSERS.put("jacop_count_values_bounds", StdDecompositions::globalCardinalityLowUp);
    DECOMPOSERS.put("jacop_nvalue", StdDecompositions::nvalue);
    DECOMPOSERS.put(
        "jacop_minimum", (b, a) -> minMax(b, b.term(a.get(0)), b.array(a.get(1)), true));
    DECOMPOSERS.put(
        "jacop_maximum", (b, a) -> minMax(b, b.term(a.get(0)), b.array(a.get(1)), false));
    DECOMPOSERS.put("jacop_minimum_arg_int", (b, a) -> argMinMax(b, a, true));
    DECOMPOSERS.put("jacop_maximum_arg_int", (b, a) -> argMinMax(b, a, false));
    DECOMPOSERS.put("jacop_member_int_reif", StdDecompositions::memberReif);
    DECOMPOSERS.put("jacop_table_int", StdDecompositions::table);
    DECOMPOSERS.put("jacop_table_bool", StdDecompositions::table);
    DECOMPOSERS.put("jacop_regular", (b, a) -> regular(b, a, false));
    DECOMPOSERS.put("jacop_cost_regular", (b, a) -> regular(b, a, true));
    DECOMPOSERS.put("jacop_lex_lesseq_int", (b, a) -> lex(b, a, false));
    DECOMPOSERS.put("jacop_lex_lesseq_bool", (b, a) -> lex(b, a, false));
    DECOMPOSERS.put("jacop_lex_less_int", (b, a) -> lex(b, a, true));
    DECOMPOSERS.put("jacop_lex_less_bool", (b, a) -> lex(b, a, true));
    DECOMPOSERS.put("jacop_lex_chain_lesseq_int", (b, a) -> lexChain(b, a, false));
    DECOMPOSERS.put("jacop_lex_chain_lesseq_bool", (b, a) -> lexChain(b, a, false));
    DECOMPOSERS.put("jacop_lex_chain_less_int", (b, a) -> lexChain(b, a, true));
    DECOMPOSERS.put("jacop_lex_chain_less_bool", (b, a) -> lexChain(b, a, true));
    DECOMPOSERS.put("jacop_increasing", (b, a) -> increasing(b, b.array(a.get(0)), false, false));
    DECOMPOSERS.put(
        "jacop_strictly_increasing", (b, a) -> increasing(b, b.array(a.get(0)), true, false));
    DECOMPOSERS.put("jacop_decreasing", (b, a) -> increasing(b, b.array(a.get(0)), false, true));
    DECOMPOSERS.put(
        "jacop_strictly_decreasing", (b, a) -> increasing(b, b.array(a.get(0)), true, true));
    DECOMPOSERS.put("jacop_value_precede_int", StdDecompositions::valuePrecede);
    DECOMPOSERS.put("jacop_circuit", (b, a) -> circuit(b, b.array(a.get(0)), 1));
    DECOMPOSERS.put(
        "jacop_circuit_offset", (b, a) -> circuit(b, b.array(a.get(0)), b.intArg(a.get(1))));
    DECOMPOSERS.put("jacop_subcircuit", (b, a) -> subcircuit(b, b.array(a.get(0))));
    DECOMPOSERS.put("jacop_assignment", StdDecompositions::inverse);
    DECOMPOSERS.put("jacop_diff2_strict", StdDecompositions::diffn);
    DECOMPOSERS.put("jacop_list_diff2", StdDecompositions::diffnNonstrict);
    DECOMPOSERS.put("jacop_cumulative", StdDecompositions::cumulative);
    DECOMPOSERS.put("jacop_cumulative_optional", StdDecompositions::cumulative);
    DECOMPOSERS.put("jacop_disjunctive_optional", StdDecompositions::disjunctiveOptional);
    DECOMPOSERS.put("jacop_networkflow", StdDecompositions::networkFlowCost);
    DECOMPOSERS.put("jacop_knapsack", StdDecompositions::knapsack);
    DECOMPOSERS.put("jacop_bin_packing", StdDecompositions::binPackingLoad);
    DECOMPOSERS.put("jacop_bin_packing_capacity", StdDecompositions::binPackingCapa);
    DECOMPOSERS.put("jacop_if_then_else_int", StdDecompositions::ifThenElse);
    DECOMPOSERS.put("jacop_if_then_else_bool", StdDecompositions::ifThenElse);
    DECOMPOSERS.put("jacop_array_var_int_element_nonshifted", StdDecompositions::elementNonshifted);
    DECOMPOSERS.put(
        "jacop_array_var_bool_element_nonshifted", StdDecompositions::elementNonshifted);
  }

  static {
    DECOMPOSERS.put("jacop_member_int", StdDecompositions::member);
    DECOMPOSERS.put("jacop_all_equal_int_reif", StdDecompositions::allEqualReif);
    DECOMPOSERS.put("jacop_minimum_arg_bool", (b, a) -> argMinMax(b, a, true));
    DECOMPOSERS.put("jacop_maximum_arg_bool", (b, a) -> argMinMax(b, a, false));
    DECOMPOSERS.put("jacop_seq_precede_chain_int", (b, a) -> seqPrecedeChain(b, b.array(a.get(0))));
    DECOMPOSERS.put("jacop_value_precede_chain_int", StdDecompositions::valuePrecedeChain);
    DECOMPOSERS.put("jacop_disjunctive_strict_optional", StdDecompositions::disjunctiveStrict);
    DECOMPOSERS.put("jacop_link_set_to_booleans", StdDecompositions::linkSetToBooleans);
    DECOMPOSERS.put("jacop_disjoint", (b, a) -> disjoint(b, a.get(0), a.get(1)));
    DECOMPOSERS.put("jacop_partition_set", StdDecompositions::partitionSet);
    DECOMPOSERS.put("jacop_if_then_else_set", StdDecompositions::ifThenElseSet);
    DECOMPOSERS.put("jacop_int_set_channel", StdDecompositions::intSetChannel);
  }

  private StdDecompositions() {}

  static boolean supports(String constraint) {
    return DECOMPOSERS.containsKey(constraint);
  }

  static Set<String> supported() {
    return DECOMPOSERS.keySet();
  }

  static void decompose(FznBuilder b, String constraint, List<Expr> args) {
    Decomposer d = DECOMPOSERS.get(constraint);
    if (d == null) {
      throw new UnsupportedOperationException("no decomposition for " + constraint);
    }
    d.decompose(b, args);
  }

  // ---------------------------------------------------------------------------------------------
  // all_different and friends.

  /** fzn_all_different_int: forall (i < j) (x[i] != x[j]). */
  static void allDifferent(FznBuilder b, List<Term> x) {
    for (int i = 0; i < x.size(); i++) {
      for (int j = i + 1; j < x.size(); j++) {
        b.ne(x.get(i), x.get(j));
      }
    }
  }

  /**
   * fzn_alldifferent_except: with bounded variables, global_cardinality_low_up over the values
   * outside the exception set with bounds 0..1, that is count(x, v) <= 1 for each such value.
   */
  static void allDifferentExcept(FznBuilder b, List<Term> x, SetLit except) {
    boolean bounded = x.stream().allMatch(b::bounded);
    if (!bounded) {
      for (int i = 0; i < x.size(); i++) {
        for (int j = i + 1; j < x.size(); j++) {
          Term both = b.and(List.of(b.inReif(x.get(i), except), b.inReif(x.get(j), except)));
          b.clause(List.of(both, b.neReif(x.get(i), x.get(j))), List.of());
        }
      }
      return;
    }
    for (long v : domainUnion(b, x)) {
      if (except.contains(v)) {
        continue;
      }
      Term c = countValue(b, x, FznBuilder.constant(v));
      b.linear(new long[] {1}, List.of(c), "le", 1);
    }
  }

  /** fzn_all_equal_int: forall (i in 2..n) (x[i - 1] = x[i]). */
  static void allEqual(FznBuilder b, List<Term> x) {
    for (int i = 1; i < x.size(); i++) {
      b.eq(x.get(i - 1), x.get(i));
    }
  }

  private static long[] domainUnion(FznBuilder b, List<Term> x) {
    TreeSet<Long> values = new TreeSet<>();
    for (Term t : x) {
      if (t.isConst()) {
        values.add(t.value());
      } else {
        SetLit d =
            b.model.domain(new FznModel.Ident(t.var())) == null
                ? SetLit.range(b.lb(t), b.ub(t))
                : b.model.domain(new FznModel.Ident(t.var()));
        for (long v : d.values()) {
          values.add(v);
        }
      }
    }
    return values.stream().mapToLong(Long::longValue).toArray();
  }

  // ---------------------------------------------------------------------------------------------
  // Counting.

  /** count(x, y) = sum (i) (bool2int(x[i] = y)), as in fzn_count_eq. */
  static Term countValue(FznBuilder b, List<Term> x, Term y) {
    List<Term> terms = new ArrayList<>();
    for (Term xi : x) {
      terms.add(b.bool2int(b.eqReif(xi, y)));
    }
    long[] ones = new long[terms.size()];
    Arrays.fill(ones, 1);
    return b.sum(ones, terms, 0);
  }

  private static Term count(FznBuilder b, List<Expr> a) {
    return countValue(b, b.array(a.get(0)), b.term(a.get(1)));
  }

  /** fzn_among: n = sum (i) (x[i] in v). */
  static void among(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    SetLit v = b.model.set(a.get(1));
    List<Term> terms = new ArrayList<>();
    long[] coefs = new long[x.size() + 1];
    for (int i = 0; i < x.size(); i++) {
      terms.add(b.bool2int(b.inReif(x.get(i), v)));
      coefs[i] = 1;
    }
    terms.add(b.term(a.get(2)));
    coefs[x.size()] = -1;
    b.linear(coefs, terms, "eq", 0);
  }

  /** fzn_global_cardinality: count(x, cover[i], counts[i]) and length(x) >= sum(counts). */
  static void globalCardinality(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    long[] cover = b.intArray(a.get(1));
    List<Term> counts = b.array(a.get(2));
    for (int i = 0; i < cover.length; i++) {
      Term c = countValue(b, x, FznBuilder.constant(cover[i]));
      b.linear(new long[] {1, -1}, List.of(c, counts.get(i)), "eq", 0);
    }
    long[] ones = new long[counts.size()];
    Arrays.fill(ones, 1);
    b.linear(ones, counts, "le", x.size());
  }

  /** fzn_global_cardinality_low_up. */
  static void globalCardinalityLowUp(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    long[] cover = b.intArray(a.get(1));
    long[] low = b.intArray(a.get(2));
    long[] up = b.intArray(a.get(3));
    for (int i = 0; i < cover.length; i++) {
      Term c = countValue(b, x, FznBuilder.constant(cover[i]));
      if (up[i] >= x.size()) {
        b.linear(new long[] {-1}, List.of(c), "le", -low[i]);
      } else if (low[i] <= 0) {
        b.linear(new long[] {1}, List.of(c), "le", up[i]);
      } else {
        b.linear(new long[] {-1}, List.of(c), "le", -low[i]);
        b.linear(new long[] {1}, List.of(c), "le", up[i]);
      }
    }
  }

  /** fzn_nvalue: n = sum (j in lb..ub) (exists (i) (x[i] = j)). */
  static void nvalue(FznBuilder b, List<Expr> a) {
    Term n = b.term(a.get(0));
    List<Term> x = b.array(a.get(1));
    if (x.isEmpty()) {
      b.eq(n, FznBuilder.constant(0));
      return;
    }
    long lo = x.stream().mapToLong(b::lb).min().getAsLong();
    long hi = x.stream().mapToLong(b::ub).max().getAsLong();
    List<Term> terms = new ArrayList<>();
    for (long j = lo; j <= hi; j++) {
      List<Term> eqs = new ArrayList<>();
      for (Term xi : x) {
        eqs.add(b.eqReif(xi, FznBuilder.constant(j)));
      }
      terms.add(b.bool2int(b.or(eqs)));
    }
    terms.add(n);
    long[] coefs = new long[terms.size()];
    Arrays.fill(coefs, 1);
    coefs[coefs.length - 1] = -1;
    b.linear(coefs, terms, "eq", 0);
  }

  // ---------------------------------------------------------------------------------------------
  // Minimum, maximum, arg_min, arg_max, member.

  /** array_int_minimum/maximum from redefinitions-2.0.mzn: y[i] = min(x[i], y[i - 1]). */
  static Term minMax(FznBuilder b, Term m, List<Term> x, boolean min) {
    long lo = x.stream().mapToLong(b::lb).min().getAsLong();
    long hi = x.stream().mapToLong(b::ub).max().getAsLong();
    Term previous = x.get(0);
    for (int i = 1; i < x.size(); i++) {
      Term y = (m != null && i == x.size() - 1) ? m : b.newInt(lo, hi);
      b.post(min ? "int_min" : "int_max", x.get(i), previous, y);
      previous = y;
    }
    if (m != null && x.size() == 1) {
      b.eq(m, previous);
    }
    return previous;
  }

  /**
   * fzn_minimum_arg_int / fzn_maximum_arg_int: w[j] = n * x[j] + j (or + (u - j)), Mx = min(w)
   * (max(w)) and (idx != j) = (Mx < w[j]) (Mx > w[j]).
   */
  static void argMinMax(FznBuilder b, List<Expr> a, boolean min) {
    List<Term> x = new ArrayList<>();
    for (Term t : b.array(a.get(0))) {
      x.add(t.bool() ? b.bool2int(t) : t);
    }
    Term idx = b.term(a.get(1));
    long l = b.intArg(a.get(2));
    long n = x.size();
    long u = l + n - 1;
    List<Term> w = new ArrayList<>();
    for (int k = 0; k < n; k++) {
      long j = l + k;
      w.add(b.sum(new long[] {n}, List.of(x.get(k)), min ? j : u - j));
    }
    Term mx = minMax(b, null, w, min);
    for (int k = 0; k < n; k++) {
      long j = l + k;
      Term ne = b.neReif(idx, FznBuilder.constant(j));
      Term cmp = min ? b.ltReif(mx, w.get(k)) : b.ltReif(w.get(k), mx);
      b.boolEq(ne, cmp);
    }
  }

  /** fzn_member_int_reif: b <-> exists (i) (x[i] = y). */
  static void memberReif(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    Term y = b.term(a.get(1));
    List<Term> eqs = new ArrayList<>();
    for (Term xi : x) {
      eqs.add(b.eqReif(xi, y));
    }
    b.boolEq(b.or(eqs), b.term(a.get(2)));
  }

  // ---------------------------------------------------------------------------------------------
  // Extensional.

  /** fzn_table_int / fzn_table_bool: var i in tuples; t_transposed[j, i] = x[j]. */
  static void table(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    List<Expr> flat = b.model.elements(a.get(1));
    int arity = x.size();
    int tuples = flat.size() / arity;
    if (tuples == 0) {
      b.fail();
      return;
    }
    Term i = b.newInt(1, tuples);
    for (int j = 0; j < arity; j++) {
      List<Term> column = new ArrayList<>();
      for (int k = 0; k < tuples; k++) {
        column.add(b.term(flat.get(k * arity + j)));
      }
      Term xj = x.get(j);
      b.post(xj.bool() ? "array_bool_element" : "array_int_element", i, column, xj);
    }
  }

  /**
   * fzn_regular and fzn_cost_regular: states a[m..n] in 1..Q, a[m] = q0, x[i] in 1..S, a[i + 1] =
   * d[a[i], x[i]], a[n] in F (and the cost chain for cost_regular). The two-dimensional access is
   * flattened as MiniZinc does it: one array_int_element on the row-major index.
   */
  static void regular(FznBuilder b, List<Expr> a, boolean cost) {
    List<Term> x = b.array(a.get(0));
    long q = b.intArg(a.get(1));
    long s = b.intArg(a.get(2));
    Expr d = a.get(3);
    long[] delta = b.intArray(d);
    long q0 = b.intArg(a.get(4));
    SetLit f = b.model.set(a.get(5));
    long minIndex = cost ? 1 : b.intArg(a.get(6));
    Expr costTable = cost ? a.get(6) : null;
    long[] costs = cost ? b.intArray(costTable) : null;
    if (x.isEmpty()) {
      if (!f.contains(q0)) {
        b.fail();
      }
      if (cost) {
        b.eq(b.term(a.get(7)), FznBuilder.constant(0));
      }
      return;
    }
    Term state = FznBuilder.constant(q0);
    Term total = FznBuilder.constant(0);
    for (Term xi : x) {
      b.in(xi, SetLit.range(1, s));
      Term next;
      Term step;
      if (state.isConst() && xi.isConst()) {
        int k = (int) ((state.value() - 1) * s + (xi.value() - minIndex));
        next = FznBuilder.constant(delta[k]);
        if (delta[k] < 1 || delta[k] > q) {
          b.fail();
        }
        step = cost ? FznBuilder.constant(costs[k]) : null;
      } else {
        Term index = b.sum(new long[] {s, 1}, List.of(state, xi), -s - minIndex + 1);
        next = b.newInt(1, q);
        b.post("array_int_element", index, d, next);
        if (cost) {
          long lo = Arrays.stream(costs).min().getAsLong();
          long hi = Arrays.stream(costs).max().getAsLong();
          step = b.newInt(lo, hi);
          b.post("array_int_element", index, costTable, step);
        } else {
          step = null;
        }
      }
      if (cost) {
        total = b.sum(new long[] {1, 1}, List.of(total, step), 0);
      }
      state = next;
    }
    b.in(state, f);
    if (cost) {
      b.eq(b.term(a.get(7)), total);
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Lexicographic ordering.

  /**
   * lex_lesseq_std_decomposition / lex_less_std_decomposition: b[i] = (x[i] <= y[i] /\ (x[i] < y[i]
   * \/ b[i + 1])), b[size + 1] = (length condition), b[0] holds.
   */
  static void lexTerms(FznBuilder b, List<Term> x, List<Term> y, boolean strict) {
    if (strict && y.isEmpty()) {
      b.fail();
      return;
    }
    if (x.isEmpty() || !strict && y.isEmpty()) {
      if (!strict && y.isEmpty() && !x.isEmpty()) {
        b.fail();
      }
      return;
    }
    int size = Math.min(x.size(), y.size()) - 1;
    Term next =
        FznBuilder.bool(strict ? x.size() - 1 < y.size() - 1 : x.size() - 1 <= y.size() - 1);
    for (int i = size; i >= 0; i--) {
      Term le = b.leReif(x.get(i), y.get(i));
      Term lt = b.ltReif(x.get(i), y.get(i));
      next = b.and(List.of(le, b.or(List.of(lt, next))));
    }
    b.require(next);
  }

  static void lex(FznBuilder b, List<Expr> a, boolean strict) {
    lexTerms(b, b.array(a.get(0)), b.array(a.get(1)), strict);
  }

  /** fzn_lex_chain_lesseq_int: lex_lesseq on consecutive columns of the matrix. */
  static void lexChain(FznBuilder b, List<Expr> a, boolean strict) {
    List<Term> flat = b.array(a.get(0));
    int vectors = (int) b.intArg(a.get(1));
    int n = flat.size() / vectors;
    for (int j = 0; j + 1 < vectors; j++) {
      List<Term> left = new ArrayList<>();
      List<Term> right = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        left.add(flat.get(i * vectors + j));
        right.add(flat.get(i * vectors + j + 1));
      }
      lexTerms(b, left, right, strict);
    }
  }

  /** fzn_increasing_int and friends: x[i - 1] <= x[i] (or <, >=, >). */
  static void increasing(FznBuilder b, List<Term> x, boolean strict, boolean decreasing) {
    for (int i = 1; i < x.size(); i++) {
      Term lo = decreasing ? x.get(i) : x.get(i - 1);
      Term hi = decreasing ? x.get(i - 1) : x.get(i);
      if (strict) {
        b.lt(lo, hi);
      } else {
        b.le(lo, hi);
      }
    }
  }

  /** fzn_value_precede_int. */
  static void valuePrecede(FznBuilder b, List<Expr> a) {
    Term before = b.term(a.get(0));
    Term after = b.term(a.get(1));
    List<Term> x = b.array(a.get(2));
    if (x.isEmpty()) {
      return;
    }
    // b[imin] = false, b[i + 1] = b[i] \/ (x[i] = before), not b[i] -> x[i] != after
    Term seen = FznBuilder.FALSE;
    for (Term xi : x) {
      Term xis = b.eqReif(xi, before);
      b.clause(List.of(seen, b.neReif(xi, after)), List.of());
      Term next = b.newBool();
      // xis -> next; not xis -> (seen = next)
      b.clause(List.of(next), List.of(xis));
      b.clause(List.of(xis, b.boolEqReif(seen, next)), List.of());
      seen = next;
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Graphs.

  /**
   * fzn_circuit: all_different(x), all_different(order), x[i] != i, order[l] = 1 and order[x[i]] =
   * if order[i] = n then 1 else order[i] + 1 endif.
   */
  static void circuit(FznBuilder b, List<Term> x, long l) {
    int n = x.size();
    if (n == 0) {
      return;
    }
    List<Term> order = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      order.add(i == 0 ? FznBuilder.constant(1) : b.newInt(1, n));
    }
    allDifferent(b, x);
    allDifferent(b, order);
    for (int i = 0; i < n; i++) {
      b.ne(x.get(i), FznBuilder.constant(l + i));
    }
    for (int i = 0; i < n; i++) {
      Term next = element(b, x.get(i), l, order);
      // next = if order[i] = n then 1 else order[i] + 1 endif
      Term last = b.eqReif(order.get(i), FznBuilder.constant(n));
      Term isOne = b.eqReif(next, FznBuilder.constant(1));
      Term succ = b.linearReif(new long[] {1, -1}, List.of(next, order.get(i)), "eq", 1);
      b.clause(List.of(isOne), List.of(last));
      b.clause(List.of(last, succ), List.of());
    }
  }

  /** Returns array[index] for an array whose index set starts at l (array_var_int_element). */
  static Term element(FznBuilder b, Term index, long l, List<Term> array) {
    long lo = array.stream().mapToLong(b::lb).min().getAsLong();
    long hi = array.stream().mapToLong(b::ub).max().getAsLong();
    Term shifted = l == 1 ? index : b.sum(new long[] {1}, List.of(index), 1 - l);
    if (shifted.isConst()) {
      if (shifted.value() < 1 || shifted.value() > array.size()) {
        b.fail();
        return array.get(0);
      }
      return array.get((int) shifted.value() - 1);
    }
    Term r = b.newInt(lo, hi);
    b.post("array_var_int_element", shifted, array, r);
    return r;
  }

  private static Term boolElement(FznBuilder b, Term index, List<Term> array) {
    if (index.isConst()) {
      return array.get((int) index.value() - 1);
    }
    Term r = b.newBool();
    b.post("array_var_bool_element", index, array, r);
    return r;
  }

  /** fzn_subcircuit, on the 1-based array that JaCoP's library passes. */
  static void subcircuit(FznBuilder b, List<Term> x) {
    int n = x.size();
    if (n == 0) {
      return;
    }
    long u = n;
    List<Term> order = new ArrayList<>();
    List<Term> ins = new ArrayList<>();
    List<Term> firstTerms = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      order.add(b.newInt(1, n));
      Term in = b.neReif(x.get(i), FznBuilder.constant(i + 1L));
      ins.add(in);
      // u + 1 + bool2int(ins[i]) * (i - u - 1)
      firstTerms.add(b.sum(new long[] {i + 1 - u - 1}, List.of(b.bool2int(in)), u + 1));
    }
    Term firstin = b.newInt(1, u + 1);
    minMax(b, firstin, firstTerms, true);
    Term lastin = b.newInt(1, u);
    Term empty = b.linearReif(new long[] {-1}, List.of(firstin), "le", -(u + 1));
    allDifferent(b, x);
    allDifferent(b, order);
    for (Term in : ins) {
      b.clause(List.of(), List.of(empty, in));
    }
    // (not empty) -> conjunction; firstin is in 1..u whenever not empty
    Term first = b.newInt(1, u);
    b.clause(List.of(empty, b.eqReif(first, firstin)), List.of());
    List<Term> conjuncts = new ArrayList<>();
    conjuncts.add(b.eqReif(element(b, first, 1, order), FznBuilder.constant(1)));
    conjuncts.add(b.ltReif(firstin, lastin));
    conjuncts.add(b.eqReif(element(b, lastin, 1, x), firstin));
    conjuncts.add(boolElement(b, lastin, ins));
    conjuncts.add(boolElement(b, first, ins));
    for (Term c : conjuncts) {
      b.clause(List.of(empty, c), List.of());
    }
    Term orderLast = element(b, lastin, 1, order);
    for (int i = 0; i < n; i++) {
      Term ne = b.neReif(x.get(i), firstin);
      Term next = element(b, x.get(i), 1, order);
      Term succ = b.linearReif(new long[] {1, -1}, List.of(next, order.get(i)), "eq", 1);
      b.clause(List.of(empty, succ), List.of(ins.get(i), ne));
      b.clause(List.of(empty, ins.get(i), b.ltReif(orderLast, order.get(i))), List.of());
    }
  }

  /** fzn_inverse: f[i] in index_set(invf) /\ invf[f[i]] = i, and the same the other way round. */
  static void inverse(FznBuilder b, List<Expr> a) {
    List<Term> f = b.array(a.get(0));
    List<Term> invf = b.array(a.get(1));
    long indexF = b.intArg(a.get(2));
    long indexInvf = b.intArg(a.get(3));
    inverseHalf(b, f, indexF, invf, indexInvf);
    inverseHalf(b, invf, indexInvf, f, indexF);
  }

  private static void inverseHalf(FznBuilder b, List<Term> f, long lf, List<Term> g, long lg) {
    for (int i = 0; i < f.size(); i++) {
      b.in(f.get(i), SetLit.range(lg, lg + g.size() - 1));
      Term gi = element(b, f.get(i), lg, g);
      b.eq(gi, FznBuilder.constant(lf + i));
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Packing and scheduling.

  /** fzn_diffn: forall (i < j) (x[i] + dx[i] <= x[j] \/ y[i] + dy[i] <= y[j] \/ ...). */
  static void diffn(FznBuilder b, List<Expr> a) {
    diffn(b, a, false);
  }

  /** fzn_diffn_nonstrict: as diffn, but a rectangle with a zero size may be placed anywhere. */
  static void diffnNonstrict(FznBuilder b, List<Expr> a) {
    diffn(b, a, true);
  }

  private static void diffn(FznBuilder b, List<Expr> a, boolean nonstrict) {
    List<Term> x = b.array(a.get(0));
    List<Term> y = b.array(a.get(1));
    List<Term> dx = b.array(a.get(2));
    List<Term> dy = b.array(a.get(3));
    for (int i = 0; i < x.size(); i++) {
      for (int j = i + 1; j < x.size(); j++) {
        List<Term> or = new ArrayList<>();
        if (nonstrict) {
          or.add(b.eqReif(dx.get(i), FznBuilder.constant(0)));
          or.add(b.eqReif(dy.get(i), FznBuilder.constant(0)));
          or.add(b.eqReif(dx.get(j), FznBuilder.constant(0)));
          or.add(b.eqReif(dy.get(j), FznBuilder.constant(0)));
        }
        or.add(before(b, x.get(i), dx.get(i), x.get(j)));
        or.add(before(b, y.get(i), dy.get(i), y.get(j)));
        or.add(before(b, x.get(j), dx.get(j), x.get(i)));
        or.add(before(b, y.get(j), dy.get(j), y.get(i)));
        b.clause(or, List.of());
      }
    }
  }

  /** s + d <= t. */
  private static Term before(FznBuilder b, Term s, Term d, Term t) {
    return b.linearReif(new long[] {1, 1, -1}, List.of(s, d, t), "le", 0);
  }

  /**
   * fzn_cumulative (and fzn_cumulative_opt_decomp for jacop_cumulative_optional): the time
   * decomposition when late - early <= 5000, otherwise the task decomposition.
   */
  static void cumulative(FznBuilder b, List<Expr> a) {
    List<Term> s = b.array(a.get(0));
    List<Term> d = b.array(a.get(1));
    List<Term> r = b.array(a.get(2));
    Term cap = b.term(a.get(3));
    List<Term> occurs = a.size() > 4 ? b.array(a.get(4)) : null;
    List<Integer> tasks = new ArrayList<>();
    for (int i = 0; i < s.size(); i++) {
      boolean mayOccur = occurs == null || !occurs.get(i).isFalse();
      if (mayOccur && b.ub(r.get(i)) > 0 && b.ub(d.get(i)) > 0) {
        tasks.add(i);
      }
    }
    if (tasks.isEmpty()) {
      if (!s.isEmpty()) {
        b.le(FznBuilder.constant(0), cap);
      }
      return;
    }
    boolean bounded = tasks.stream().allMatch(i -> b.bounded(s.get(i)) && b.bounded(d.get(i)));
    long early = Long.MAX_VALUE;
    long late = Long.MIN_VALUE;
    for (int i : tasks) {
      early = Math.min(early, b.lb(s.get(i)));
      late = Math.max(late, b.ub(s.get(i)) + b.ub(d.get(i)));
    }
    if (bounded && late - early <= 5000) {
      for (long t = early; t <= late; t++) {
        List<Term> load = new ArrayList<>();
        for (int i : tasks) {
          // s[i] <= t /\ t < s[i] + d[i]
          List<Term> conj = new ArrayList<>();
          if (occurs != null) {
            conj.add(occurs.get(i));
          }
          conj.add(b.linearReif(new long[] {1}, List.of(s.get(i)), "le", t));
          conj.add(b.linearReif(new long[] {-1, -1}, List.of(s.get(i), d.get(i)), "le", -t - 1));
          load.add(b.times(b.bool2int(b.and(conj)), r.get(i)));
        }
        capacity(b, load, cap);
      }
    } else {
      for (int j : tasks) {
        List<Term> load = new ArrayList<>();
        for (int i : tasks) {
          List<Term> conj = new ArrayList<>();
          if (occurs != null && i != j) {
            conj.add(occurs.get(i));
          }
          if (i == j && occurs == null) {
            // s[j] <= s[j] /\ s[j] < s[j] + d[j]
            conj.add(b.linearReif(new long[] {-1}, List.of(d.get(j)), "le", -1));
          } else if (i != j) {
            conj.add(b.leReif(s.get(i), s.get(j)));
            conj.add(
                b.linearReif(
                    new long[] {1, -1, -1}, List.of(s.get(j), s.get(i), d.get(i)), "le", -1));
          }
          load.add(b.times(b.bool2int(b.and(conj)), r.get(i)));
        }
        if (occurs == null) {
          capacity(b, load, cap);
        } else {
          // occurs(s[j]) -> b >= r[j] + sum (...)
          long[] coefs = new long[load.size() + 1];
          Arrays.fill(coefs, 1);
          coefs[load.size()] = -1;
          List<Term> terms = new ArrayList<>(load);
          terms.add(cap);
          b.clause(List.of(b.linearReif(coefs, terms, "le", 0)), List.of(occurs.get(j)));
        }
      }
    }
  }

  private static void capacity(FznBuilder b, List<Term> load, Term cap) {
    long[] coefs = new long[load.size() + 1];
    Arrays.fill(coefs, 1);
    coefs[load.size()] = -1;
    List<Term> terms = new ArrayList<>(load);
    terms.add(cap);
    b.linear(coefs, terms, "le", 0);
  }

  /**
   * fzn_disjunctive_opt: forall (i < j) (absent(s[i]) \/ absent(s[j]) \/ d[i] = 0 \/ d[j] = 0 \/
   * s[i] + d[i] <= s[j] \/ s[j] + d[j] <= s[i]); JaCoP's library also posts d[i] >= 0.
   */
  static void disjunctiveOptional(FznBuilder b, List<Expr> a) {
    List<Term> s = b.array(a.get(0));
    List<Term> d = b.array(a.get(1));
    List<Term> occurs = b.array(a.get(2));
    for (int i = 0; i < s.size(); i++) {
      for (int j = i + 1; j < s.size(); j++) {
        List<Term> or = new ArrayList<>();
        or.add(b.eqReif(d.get(i), FznBuilder.constant(0)));
        or.add(b.eqReif(d.get(j), FznBuilder.constant(0)));
        or.add(before(b, s.get(i), d.get(i), s.get(j)));
        or.add(before(b, s.get(j), d.get(j), s.get(i)));
        b.clause(or, List.of(occurs.get(i), occurs.get(j)));
      }
    }
  }

  /**
   * fzn_network_flow_cost: cost = sum (flow[i] * weight[i]) and, for each node, outflow - inflow =
   * balance. Arcs are numbered like the balance array (from 1), as JaCoP's library passes them.
   */
  static void networkFlowCost(FznBuilder b, List<Expr> a) {
    long[] arc = b.intArray(a.get(0));
    List<Term> flow = b.array(a.get(1));
    List<Term> weight = b.array(a.get(2));
    long[] balance = b.intArray(a.get(3));
    Term cost = b.term(a.get(4));
    long shift = 1 - Math.min(1, Arrays.stream(arc).min().orElse(1));
    List<Term> products = new ArrayList<>();
    for (int i = 0; i < flow.size(); i++) {
      products.add(b.times(flow.get(i), weight.get(i)));
    }
    long[] coefs = new long[products.size() + 1];
    Arrays.fill(coefs, 1);
    coefs[products.size()] = -1;
    List<Term> terms = new ArrayList<>(products);
    terms.add(cost);
    b.linear(coefs, terms, "eq", 0);
    for (int node = 1; node <= balance.length; node++) {
      List<Long> c = new ArrayList<>();
      List<Term> f = new ArrayList<>();
      for (int j = 0; j < flow.size(); j++) {
        if (arc[2 * j] + shift == node) {
          c.add(1L);
          f.add(flow.get(j));
        }
        if (arc[2 * j + 1] + shift == node) {
          c.add(-1L);
          f.add(flow.get(j));
        }
      }
      b.linear(c.stream().mapToLong(Long::longValue).toArray(), f, "eq", balance[node - 1]);
    }
  }

  /**
   * fzn_knapsack: x[i] >= 0, W >= 0, P >= 0, P = sum (x[i] * p[i]), W = sum (x[i] * w[i]). JaCoP's
   * library passes only the items with a positive weight and profit to jacop_knapsack.
   */
  static void knapsack(FznBuilder b, List<Expr> a) {
    long[] w = b.intArray(a.get(0));
    long[] p = b.intArray(a.get(1));
    Term weight = b.term(a.get(2));
    Term profit = b.term(a.get(3));
    List<Term> x = b.array(a.get(4));
    for (Term xi : x) {
      b.le(FznBuilder.constant(0), xi);
    }
    b.le(FznBuilder.constant(0), weight);
    b.le(FznBuilder.constant(0), profit);
    List<Term> terms = new ArrayList<>(x);
    terms.add(profit);
    long[] coefs = Arrays.copyOf(p, x.size() + 1);
    coefs[x.size()] = -1;
    b.linear(coefs, terms, "eq", 0);
    terms = new ArrayList<>(x);
    terms.add(weight);
    coefs = Arrays.copyOf(w, x.size() + 1);
    coefs[x.size()] = -1;
    b.linear(coefs, terms, "eq", 0);
  }

  /**
   * fzn_bin_packing_load: sum(load) = sum(w), bin[i] in index_set(load) and load[b] = sum (w[i] *
   * (bin[i] = b)).
   */
  static void binPackingLoad(FznBuilder b, List<Expr> a) {
    List<Term> bin = b.array(a.get(0));
    List<Term> load = b.array(a.get(1));
    long[] w = b.intArray(a.get(2));
    long first = b.intArg(a.get(3));
    long[] ones = new long[load.size()];
    Arrays.fill(ones, 1);
    b.linear(ones, load, "eq", Arrays.stream(w).sum());
    for (Term bi : bin) {
      b.in(bi, SetLit.range(first, first + load.size() - 1));
    }
    for (int k = 0; k < load.size(); k++) {
      List<Term> terms = new ArrayList<>();
      long[] coefs = new long[bin.size() + 1];
      for (int i = 0; i < bin.size(); i++) {
        terms.add(b.bool2int(b.eqReif(bin.get(i), FznBuilder.constant(first + k))));
        coefs[i] = w[i];
      }
      terms.add(load.get(k));
      coefs[bin.size()] = -1;
      b.linear(coefs, terms, "eq", 0);
    }
  }

  /** fzn_bin_packing_capa: bin[i] in index_set(c) and c[b] >= sum (w[i] * (bin[i] = b)). */
  static void binPackingCapa(FznBuilder b, List<Expr> a) {
    List<Term> bin = b.array(a.get(0));
    long[] capacity = b.intArray(a.get(1));
    long[] w = b.intArray(a.get(2));
    long first = b.intArg(a.get(3));
    for (Term bi : bin) {
      b.in(bi, SetLit.range(first, first + capacity.length - 1));
    }
    for (int k = 0; k < capacity.length; k++) {
      List<Term> terms = new ArrayList<>();
      for (Term bi : bin) {
        terms.add(b.bool2int(b.eqReif(bi, FznBuilder.constant(first + k))));
      }
      b.linear(w, terms, "le", capacity[k]);
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Conditionals and element.

  /**
   * fzn_if_then_else_int / _bool (and the _var forms): d[1] = true, d[i] = (not c[i - 1] /\ d[i -
   * 1]) and c[i] /\ d[i] -> y = x[i].
   */
  static void ifThenElse(FznBuilder b, List<Expr> a) {
    List<Term> c = b.array(a.get(0));
    List<Term> x = b.array(a.get(1));
    Term y = b.term(a.get(2));
    Term d = FznBuilder.TRUE;
    for (int i = 0; i < c.size(); i++) {
      if (i > 0) {
        d = b.and(List.of(b.not(c.get(i - 1)), d));
      }
      b.clause(List.of(b.eqReif(y, x.get(i))), List.of(c.get(i), d));
    }
  }

  /**
   * array_var_int_element_nonshifted (redefinitions-2.0.2.mzn without JaCoP's library):
   * array_var_int_element(idx - (min_index - 1), xs, y).
   */
  static void elementNonshifted(FznBuilder b, List<Expr> a) {
    Term idx = b.term(a.get(0));
    List<Term> xs = b.array(a.get(1));
    Term y = b.term(a.get(2));
    long minIndex = b.intArg(a.get(3));
    Term shifted = b.sum(new long[] {1}, List.of(idx), 1 - minIndex);
    b.post(y.bool() ? "array_var_bool_element" : "array_var_int_element", shifted, xs, y);
  }

  // ---------------------------------------------------------------------------------------------
  // Further integer globals.

  /** fzn_member_int: exists (i) (x[i] = y). */
  static void member(FznBuilder b, List<Expr> a) {
    Term y = b.term(a.get(1));
    List<Term> eqs = new ArrayList<>();
    for (Term xi : b.array(a.get(0))) {
      eqs.add(b.eqReif(xi, y));
    }
    b.require(b.or(eqs));
  }

  /** fzn_all_equal_int_reif: b <-> forall (i < j) (x[i] = x[j]). */
  static void allEqualReif(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    List<Term> eqs = new ArrayList<>();
    for (int i = 0; i < x.size(); i++) {
      for (int j = i + 1; j < x.size(); j++) {
        eqs.add(b.eqReif(x.get(i), x.get(j)));
      }
    }
    b.boolEq(b.and(eqs), b.term(a.get(1)));
  }

  /**
   * fzn_seq_precede_chain_int: H[f] <= 1, H[f] = max(x[f], 0), H[i] <= H[i - 1] + 1 and H[i] =
   * max(x[i], H[i - 1]).
   */
  static void seqPrecedeChain(FznBuilder b, List<Term> x) {
    if (x.isEmpty()) {
      return;
    }
    long lo = x.stream().mapToLong(b::lb).min().getAsLong();
    long hi = x.stream().mapToLong(b::ub).max().getAsLong();
    Term previous = null;
    for (Term xi : x) {
      Term h = b.newInt(lo, hi);
      if (previous == null) {
        b.linear(new long[] {1}, List.of(h), "le", 1);
        b.post("int_max", xi, FznBuilder.constant(0), h);
      } else {
        b.linear(new long[] {1, -1}, List.of(h, previous), "le", 1);
        b.post("int_max", xi, previous, h);
      }
      previous = h;
    }
  }

  /**
   * fzn_value_precede_chain_int: Y[i] = p[x[i] - l + 1], where p maps a value to its position in
   * the chain (0 for values not in it), and seq_precede_chain(Y).
   */
  static void valuePrecedeChain(FznBuilder b, List<Expr> a) {
    long[] order = b.intArray(a.get(0));
    List<Term> x = b.array(a.get(1));
    if (order.length == 0 || x.isEmpty()) {
      return;
    }
    long l = x.stream().mapToLong(b::lb).min().getAsLong();
    long u = x.stream().mapToLong(b::ub).max().getAsLong();
    long[] p = new long[(int) (u - l + 1)];
    for (int i = 0; i < order.length; i++) {
      if (order[i] >= l && order[i] <= u) {
        p[(int) (order[i] - l)] += i + 1;
      }
    }
    List<Term> y = new ArrayList<>();
    for (Term xi : x) {
      if (xi.isConst()) {
        y.add(FznBuilder.constant(p[(int) (xi.value() - l)]));
      } else {
        Term yi = b.newInt(0, order.length);
        b.post("array_int_element", b.sum(new long[] {1}, List.of(xi), 1 - l), p, yi);
        y.add(yi);
      }
    }
    seqPrecedeChain(b, y);
  }

  /**
   * fzn_disjunctive_strict_opt_decomp: d[i] >= 0 and forall (i < j) (absent(s[i]) \/ absent(s[j])
   * \/ s[i] + d[i] <= s[j] \/ s[j] + d[j] <= s[i]).
   */
  static void disjunctiveStrict(FznBuilder b, List<Expr> a) {
    List<Term> s = b.array(a.get(0));
    List<Term> d = b.array(a.get(1));
    List<Term> occurs = b.array(a.get(2));
    for (Term di : d) {
      b.le(FznBuilder.constant(0), di);
    }
    for (int i = 0; i < s.size(); i++) {
      for (int j = i + 1; j < s.size(); j++) {
        List<Term> or = new ArrayList<>();
        or.add(before(b, s.get(i), d.get(i), s.get(j)));
        or.add(before(b, s.get(j), d.get(j), s.get(i)));
        b.clause(or, List.of(occurs.get(i), occurs.get(j)));
      }
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Set globals.

  /** fzn_link_set_to_booleans: b[i] <-> i in s, with b indexed from offset. */
  static void linkSetToBooleans(FznBuilder b, List<Expr> a) {
    String s = b.set(a.get(0));
    List<Term> bs = b.array(a.get(1));
    long offset = b.intArg(a.get(2));
    for (int i = 0; i < bs.size(); i++) {
      b.post("set_in_reif", offset + i, s, bs.get(i));
    }
  }

  /** fzn_disjoint: s intersect t = {}. */
  static void disjoint(FznBuilder b, Expr s, Expr t) {
    SetLit universe = b.universe(s);
    if (universe == null) {
      throw new UnsupportedOperationException("set without a universe");
    }
    String r = b.newSet(universe);
    b.post("set_intersect", b.set(s), b.set(t), r);
    b.post("set_eq", r, "{}");
  }

  /** fzn_partition_set: all_disjoint(x) and universe = array_union(x). */
  static void partitionSet(FznBuilder b, List<Expr> a) {
    List<Expr> xs = b.model.elements(a.get(0));
    String universe = b.set(a.get(1));
    for (int i = 0; i < xs.size(); i++) {
      for (int j = i + 1; j < xs.size(); j++) {
        disjoint(b, xs.get(i), xs.get(j));
      }
    }
    SetLit all = unionOf(b, xs);
    String union = b.set(xs.get(0));
    for (int i = 1; i < xs.size(); i++) {
      String r = b.newSet(all);
      b.post("set_union", union, b.set(xs.get(i)), r);
      union = r;
    }
    b.post("set_eq", union, universe);
  }

  private static SetLit unionOf(FznBuilder b, List<Expr> xs) {
    TreeSet<Long> values = new TreeSet<>();
    for (Expr x : xs) {
      SetLit u = b.universe(x);
      if (u == null) {
        throw new UnsupportedOperationException("set without a universe");
      }
      for (long v : u.values()) {
        values.add(v);
      }
    }
    return SetLit.of(values.stream().mapToLong(Long::longValue).toArray());
  }

  /** fzn_if_then_else_set / fzn_if_then_else_var_set. */
  static void ifThenElseSet(FznBuilder b, List<Expr> a) {
    List<Term> c = b.array(a.get(0));
    List<Expr> x = b.model.elements(a.get(1));
    String y = b.set(a.get(2));
    Term d = FznBuilder.TRUE;
    for (int i = 0; i < c.size(); i++) {
      if (i > 0) {
        d = b.and(List.of(b.not(c.get(i - 1)), d));
      }
      Term eq = b.newBool();
      b.post("set_eq_reif", y, b.set(x.get(i)), eq);
      b.clause(List.of(eq), List.of(c.get(i), d));
    }
  }

  /**
   * fzn_int_set_channel: x[i] in index_set(y), y[j] subset index_set(x) and x[i] = j <-> i in y[j],
   * with the index sets starting at xoff and yoff.
   */
  static void intSetChannel(FznBuilder b, List<Expr> a) {
    List<Term> x = b.array(a.get(0));
    List<Expr> y = b.model.elements(a.get(1));
    long xoff = b.intArg(a.get(2));
    long yoff = b.intArg(a.get(3));
    for (Term xi : x) {
      b.in(xi, SetLit.range(yoff, yoff + y.size() - 1));
    }
    for (Expr yj : y) {
      b.post("set_subset", b.set(yj), SetLit.range(xoff, xoff + x.size() - 1));
    }
    for (int i = 0; i < x.size(); i++) {
      for (int j = 0; j < y.size(); j++) {
        Term eq = b.eqReif(x.get(i), FznBuilder.constant(yoff + j));
        Term in = b.newBool();
        b.post("set_in_reif", xoff + i, b.set(y.get(j)), in);
        b.boolEq(eq, in);
      }
    }
  }
}
