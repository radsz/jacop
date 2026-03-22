/*
 * ConstraintFncs.java This file is part of JaCoP.
 *
 * <p>JaCoP is a Java Constraint Programming solver.
 *
 * <p>Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 * <p>This program is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Affero General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * <p>This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * <p>Notwithstanding any other provision of this License, the copyright owners of this work
 * supplement the terms of this License with terms prohibiting misrepresentation of the origin of
 * this work and requiring that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license terms is in accordance with
 * Section 7 of GNU Affero General Public License version 3.
 *
 * <p>You should have received a copy of the GNU Affero General Public License along with this
 * program. If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.fz.constraints;

import org.jacop.fz.SimpleNode;

/** Registry of constraint generation functions for flatzinc. */
public final class ConstraintFncs {

  final BoolConstraints bc;
  final ComparisonConstraints cc;
  final LinearConstraints lc;
  final OperationConstraints oc;
  final ElementConstraints ec;
  final GlobalConstraints gc;
  final GraphConstraints graph;
  final SetConstraints sc;
  final FloatComparisonConstraints fcc;
  final FloatLinearConstraints flc;
  final FloatOperationConstraints foc;

  /**
   * Constructs the constraint functions registry.
   *
   * @param support the support object for constraint generation
   */
  public ConstraintFncs(Support support) {

    bc = new BoolConstraints(support);
    cc = new ComparisonConstraints(support);
    lc = new LinearConstraints(support);
    oc = new OperationConstraints(support);
    ec = new ElementConstraints(support);
    gc = new GlobalConstraints(support);
    sc = new SetConstraints(support);
    fcc = new FloatComparisonConstraints(support);
    flc = new FloatLinearConstraints(support);
    foc = new FloatOperationConstraints(support);
    graph = new GraphConstraints(support);
  }

  // Boolean constraints
  /** Handles the array_bool_and FlatZinc constraint. */
  public void array_bool_and(SimpleNode n) {
    bc.gen_array_bool_and(n);
  }

  /** Handles the array_bool_and_imp FlatZinc constraint. */
  public void array_bool_and_imp(SimpleNode n) {
    bc.gen_array_bool_and_imp(n);
  }

  /** Handles the array_bool_or FlatZinc constraint. */
  public void array_bool_or(SimpleNode n) {
    bc.gen_array_bool_or(n);
  }

  /** Handles the array_bool_or_imp FlatZinc constraint. */
  public void array_bool_or_imp(SimpleNode n) {
    bc.gen_array_bool_or_imp(n);
  }

  /** Handles the array_bool_xor FlatZinc constraint. */
  public void array_bool_xor(SimpleNode n) {
    bc.gen_array_bool_xor(n);
  }

  /** Handles the array_bool_xor_imp FlatZinc constraint. */
  public void array_bool_xor_imp(SimpleNode n) {
    bc.gen_array_bool_xor_imp(n);
  }

  /** Handles the bool_and FlatZinc constraint. */
  public void bool_and(SimpleNode n) {
    bc.gen_bool_and(n);
  }

  /** Handles the bool_and_imp FlatZinc constraint. */
  public void bool_and_imp(SimpleNode n) {
    bc.gen_bool_and_imp(n);
  }

  /** Handles the bool_not FlatZinc constraint. */
  public void bool_not(SimpleNode n) {
    bc.gen_bool_not(n);
  }

  /** Handles the bool_or FlatZinc constraint. */
  public void bool_or(SimpleNode n) {
    bc.gen_bool_or(n);
  }

  /** Handles the bool_xor FlatZinc constraint. */
  public void bool_xor(SimpleNode n) {
    bc.gen_bool_xor(n);
  }

  /** Handles the bool_xor_imp FlatZinc constraint. */
  public void bool_xor_imp(SimpleNode n) {
    bc.gen_bool_xor_imp(n);
  }

  /** Handles the bool_clause FlatZinc constraint. */
  public void bool_clause(SimpleNode n) {
    bc.gen_bool_clause(n);
  }

  /** Handles the bool_clause_reif FlatZinc constraint. */
  public void bool_clause_reif(SimpleNode n) {
    bc.gen_bool_clause_reif(n);
  }

  /** Handles the bool_clause_imp FlatZinc constraint. */
  public void bool_clause_imp(SimpleNode n) {
    bc.gen_bool_clause_imp(n);
  }

  /** Handles the bool2int FlatZinc constraint. */
  public void bool2int(SimpleNode n) {
    bc.gen_bool2int(n);
  }

  // Comparisons boolean and int
  /** Handles the bool_eq FlatZinc constraint. */
  public void bool_eq(SimpleNode n) {
    cc.gen_bool_eq(n);
  }

  /** Handles the bool_eq_reif FlatZinc constraint. */
  public void bool_eq_reif(SimpleNode n) {
    cc.gen_bool_eq_reif(n);
  }

  /** Handles the bool_eq_imp FlatZinc constraint. */
  public void bool_eq_imp(SimpleNode n) {
    cc.gen_bool_eq_imp(n);
  }

  /** Handles the bool_ne FlatZinc constraint. */
  public void bool_ne(SimpleNode n) {
    cc.gen_bool_ne(n);
  }

  /** Handles the bool_ne_reif FlatZinc constraint. */
  public void bool_ne_reif(SimpleNode n) {
    cc.gen_bool_ne_reif(n);
  }

  /** Handles the bool_ne_imp FlatZinc constraint. */
  public void bool_ne_imp(SimpleNode n) {
    cc.gen_bool_ne_imp(n);
  }

  /** Handles the bool_le FlatZinc constraint. */
  public void bool_le(SimpleNode n) {
    cc.gen_bool_le(n);
  }

  /** Handles the bool_le_reif FlatZinc constraint. */
  public void bool_le_reif(SimpleNode n) {
    cc.gen_bool_le_reif(n);
  }

  /** Handles the bool_le_imp FlatZinc constraint. */
  public void bool_le_imp(SimpleNode n) {
    cc.gen_bool_le_imp(n);
  }

  /** Handles the bool_lt FlatZinc constraint. */
  public void bool_lt(SimpleNode n) {
    cc.gen_bool_lt(n);
  }

  /** Handles the bool_lt_reif FlatZinc constraint. */
  public void bool_lt_reif(SimpleNode n) {
    cc.gen_bool_lt_reif(n);
  }

  /** Handles the bool_lt_imp FlatZinc constraint. */
  public void bool_lt_imp(SimpleNode n) {
    cc.gen_bool_lt_imp(n);
  }

  /** Handles the bool_gt_imp FlatZinc constraint. */
  public void bool_gt_imp(SimpleNode n) {
    cc.gen_bool_gt_imp(n);
  }

  /** Handles the bool_ge_imp FlatZinc constraint. */
  public void bool_ge_imp(SimpleNode n) {
    cc.gen_bool_ge_imp(n);
  }

  /** Handles the int_eq FlatZinc constraint. */
  public void int_eq(SimpleNode n) {
    cc.gen_int_eq(n);
  }

  /** Handles the int_eq_reif FlatZinc constraint. */
  public void int_eq_reif(SimpleNode n) {
    cc.gen_int_eq_reif(n);
  }

  /** Handles the int_eq_imp FlatZinc constraint. */
  public void int_eq_imp(SimpleNode n) {
    cc.gen_int_eq_imp(n);
  }

  /** Handles the int_ne FlatZinc constraint. */
  public void int_ne(SimpleNode n) {
    cc.gen_int_ne(n);
  }

  /** Handles the int_ne_reif FlatZinc constraint. */
  public void int_ne_reif(SimpleNode n) {
    cc.gen_int_ne_reif(n);
  }

  /** Handles the int_ne_imp FlatZinc constraint. */
  public void int_ne_imp(SimpleNode n) {
    cc.gen_int_ne_imp(n);
  }

  /** Handles the int_le FlatZinc constraint. */
  public void int_le(SimpleNode n) {
    cc.gen_int_le(n);
  }

  /** Handles the int_le_reif FlatZinc constraint. */
  public void int_le_reif(SimpleNode n) {
    cc.gen_int_le_reif(n);
  }

  /** Handles the int_le_imp FlatZinc constraint. */
  public void int_le_imp(SimpleNode n) {
    cc.gen_int_le_imp(n);
  }

  /** Handles the int_lt FlatZinc constraint. */
  public void int_lt(SimpleNode n) {
    cc.gen_int_lt(n);
  }

  /** Handles the int_lt_reif FlatZinc constraint. */
  public void int_lt_reif(SimpleNode n) {
    cc.gen_int_lt_reif(n);
  }

  /** Handles the int_lt_imp FlatZinc constraint. */
  public void int_lt_imp(SimpleNode n) {
    cc.gen_int_lt_imp(n);
  }

  /** Handles the int_gt_imp FlatZinc constraint. */
  public void int_gt_imp(SimpleNode n) {
    cc.gen_int_gt_imp(n);
  }

  /** Handles the int_ge_imp FlatZinc constraint. */
  public void int_ge_imp(SimpleNode n) {
    cc.gen_int_ge_imp(n);
  }

  // Linear bool and int constraints
  /** Handles the bool_lin_eq FlatZinc constraint. */
  public void bool_lin_eq(SimpleNode n) {
    lc.gen_bool_lin_eq(n);
  }

  /** Handles the bool_lin_eq_reif FlatZinc constraint. */
  public void bool_lin_eq_reif(SimpleNode n) {
    lc.gen_int_lin_eq_reif(n);
  }

  /** Handles the bool_lin_ne FlatZinc constraint. */
  public void bool_lin_ne(SimpleNode n) {
    lc.gen_int_lin_ne(n);
  }

  /** Handles the bool_lin_ne_reif FlatZinc constraint. */
  public void bool_lin_ne_reif(SimpleNode n) {
    lc.gen_int_lin_ne_reif(n);
  }

  /** Handles the bool_lin_lt FlatZinc constraint. */
  public void bool_lin_lt(SimpleNode n) {
    lc.gen_int_lin_lt(n);
  }

  /** Handles the bool_lin_lt_reif FlatZinc constraint. */
  public void bool_lin_lt_reif(SimpleNode n) {
    lc.gen_int_lin_lt_reif(n);
  }

  /** Handles the bool_lin_le FlatZinc constraint. */
  public void bool_lin_le(SimpleNode n) {
    lc.gen_int_lin_le(n);
  }

  /** Handles the bool_lin_le_reif FlatZinc constraint. */
  public void bool_lin_le_reif(SimpleNode n) {
    lc.gen_int_lin_le_reif(n);
  }

  /** Handles the int_lin_eq FlatZinc constraint. */
  public void int_lin_eq(SimpleNode n) {
    lc.gen_int_lin_eq(n);
  }

  /** Handles the int_lin_eq_reif FlatZinc constraint. */
  public void int_lin_eq_reif(SimpleNode n) {
    lc.gen_int_lin_eq_reif(n);
  }

  /** Handles the int_lin_eq_imp FlatZinc constraint. */
  public void int_lin_eq_imp(SimpleNode n) {
    lc.gen_int_lin_eq_imp(n);
  }

  /** Handles the int_lin_ne FlatZinc constraint. */
  public void int_lin_ne(SimpleNode n) {
    lc.gen_int_lin_ne(n);
  }

  /** Handles the int_lin_ne_reif FlatZinc constraint. */
  public void int_lin_ne_reif(SimpleNode n) {
    lc.gen_int_lin_ne_reif(n);
  }

  /** Handles the int_lin_ne_imp FlatZinc constraint. */
  public void int_lin_ne_imp(SimpleNode n) {
    lc.gen_int_lin_ne_imp(n);
  }

  /** Handles the int_lin_lt FlatZinc constraint. */
  public void int_lin_lt(SimpleNode n) {
    lc.gen_int_lin_lt(n);
  }

  /** Handles the int_lin_lt_reif FlatZinc constraint. */
  public void int_lin_lt_reif(SimpleNode n) {
    lc.gen_int_lin_lt_reif(n);
  }

  /** Handles the int_lin_lt_imp FlatZinc constraint. */
  public void int_lin_lt_imp(SimpleNode n) {
    lc.gen_int_lin_lt_imp(n);
  }

  /** Handles the int_lin_le FlatZinc constraint. */
  public void int_lin_le(SimpleNode n) {
    lc.gen_int_lin_le(n);
  }

  /** Handles the int_lin_le_reif FlatZinc constraint. */
  public void int_lin_le_reif(SimpleNode n) {
    lc.gen_int_lin_le_reif(n);
  }

  /** Handles the int_lin_le_imp FlatZinc constraint. */
  public void int_lin_le_imp(SimpleNode n) {
    lc.gen_int_lin_le_imp(n);
  }

  /** Handles the int_lin_gt_imp FlatZinc constraint. */
  public void int_lin_gt_imp(SimpleNode n) {
    lc.gen_int_lin_gt_imp(n);
  }

  /** Handles the int_lin_ge_imp FlatZinc constraint. */
  public void int_lin_ge_imp(SimpleNode n) {
    lc.gen_int_lin_ge_imp(n);
  }

  // Diverse int operations
  /** Handles the int_min FlatZinc constraint. */
  public void int_min(SimpleNode n) {
    oc.gen_int_min(n);
  }

  /** Handles the int_max FlatZinc constraint. */
  public void int_max(SimpleNode n) {
    oc.gen_int_max(n);
  }

  /** Handles the int_mod FlatZinc constraint. */
  public void int_mod(SimpleNode n) {
    oc.gen_int_mod(n);
  }

  /** Handles the int_div FlatZinc constraint. */
  public void int_div(SimpleNode n) {
    oc.gen_int_div(n);
  }

  /** Handles the int_abs FlatZinc constraint. */
  public void int_abs(SimpleNode n) {
    oc.gen_int_abs(n);
  }

  /** Handles the int_times FlatZinc constraint. */
  public void int_times(SimpleNode n) {
    oc.gen_int_times(n);
  }

  /** Handles the int_plus FlatZinc constraint. */
  public void int_plus(SimpleNode n) {
    oc.gen_int_plus(n);
  }

  /** Handles the int_pow FlatZinc constraint. */
  public void int_pow(SimpleNode n) {
    oc.gen_int_pow(n);
  }

  /** Handles the int2float FlatZinc constraint. */
  public void int2float(SimpleNode n) {
    oc.gen_int2float(n);
  }

  // Element int, boolean, set and float constraints
  /** Handles the array_bool_element FlatZinc constraint. */
  public void array_bool_element(SimpleNode n) {
    ec.gen_array_bool_element(n);
  }

  /** Handles the array_var_bool_element FlatZinc constraint. */
  public void array_var_bool_element(SimpleNode n) {
    ec.gen_array_var_int_element(n);
  }

  /** Handles the array_int_element FlatZinc constraint. */
  public void array_int_element(SimpleNode n) {
    ec.gen_array_int_element(n);
  }

  /** Handles the array_var_int_element FlatZinc constraint. */
  public void array_var_int_element(SimpleNode n) {
    ec.gen_array_var_int_element(n);
  }

  /** Handles the array_set_element FlatZinc constraint. */
  public void array_set_element(SimpleNode n) {
    ec.gen_array_set_element(n);
  }

  /** Handles the array_var_set_element FlatZinc constraint. */
  public void array_var_set_element(SimpleNode n) {
    ec.gen_array_var_set_element(n);
  }

  /** Handles the array_float_element FlatZinc constraint. */
  public void array_float_element(SimpleNode n) {
    ec.gen_array_float_element(n);
  }

  /** Handles the array_var_float_element FlatZinc constraint. */
  public void array_var_float_element(SimpleNode n) {
    ec.gen_array_var_float_element(n);
  }

  // Global constraints
  /** Handles the jacop_cumulative FlatZinc constraint. */
  public void jacop_cumulative(SimpleNode n) {
    gc.gen_jacop_cumulative(n);
  }

  /** Handles the jacop_circuit FlatZinc constraint. */
  public void jacop_circuit(SimpleNode n) {
    gc.gen_jacop_circuit(n);
  }

  /** Handles the jacop_subcircuit FlatZinc constraint. */
  public void jacop_subcircuit(SimpleNode n) {
    gc.gen_jacop_subcircuit(n);
  }

  /** Handles the jacop_alldiff FlatZinc constraint. */
  public void jacop_alldiff(SimpleNode n) {
    gc.gen_jacop_alldiff(n);
  }

  /** Handles the jacop_softalldiff FlatZinc constraint. */
  public void jacop_softalldiff(SimpleNode n) {
    gc.gen_jacop_softalldiff(n);
  }

  /** Handles the jacop_softgcc FlatZinc constraint. */
  public void jacop_softgcc(SimpleNode n) {
    gc.gen_jacop_softgcc(n);
  }

  /** Handles the jacop_alldistinct FlatZinc constraint. */
  public void jacop_alldistinct(SimpleNode n) {
    gc.gen_jacop_alldistinct(n);
  }

  /** Handles the jacop_alldifferent_except_0 FlatZinc constraint. */
  public void jacop_alldifferent_except_0(SimpleNode n) {
    gc.gen_jacop_alldifferent_except_0(n);
  }

  /** Handles the jacop_alldifferent_except FlatZinc constraint. */
  public void jacop_alldifferent_except(SimpleNode n) {
    gc.gen_jacop_alldifferent_except(n);
  }

  /** Handles the jacop_among_var FlatZinc constraint. */
  public void jacop_among_var(SimpleNode n) {
    gc.gen_jacop_among_var(n);
  }

  /** Handles the jacop_among FlatZinc constraint. */
  public void jacop_among(SimpleNode n) {
    gc.gen_jacop_among(n);
  }

  /** Handles the jacop_gcc FlatZinc constraint. */
  public void jacop_gcc(SimpleNode n) {
    gc.gen_jacop_gcc(n);
  }

  /** Handles the jacop_global_cardinality_closed FlatZinc constraint. */
  public void jacop_global_cardinality_closed(SimpleNode n) {
    gc.gen_jacop_global_cardinality_closed(n);
  }

  /** Handles the jacop_global_cardinality_low_up_closed FlatZinc constraint. */
  public void jacop_global_cardinality_low_up_closed(SimpleNode n) {
    gc.gen_jacop_global_cardinality_low_up_closed(n);
  }

  /** Handles the jacop_diff2_strict FlatZinc constraint. */
  public void jacop_diff2_strict(SimpleNode n) {
    gc.gen_jacop_diff2_strict(n);
  }

  /** Handles the jacop_diff2 FlatZinc constraint. */
  public void jacop_diff2(SimpleNode n) {
    gc.gen_jacop_diff2(n);
  }

  /** Handles the jacop_list_diff2 FlatZinc constraint. */
  public void jacop_list_diff2(SimpleNode n) {
    gc.gen_jacop_list_diff2(n);
  }

  /** Handles the jacop_count FlatZinc constraint. */
  public void jacop_count(SimpleNode n) {
    gc.gen_jacop_count(n);
  }

  /** Handles the jacop_count_reif FlatZinc constraint. */
  public void jacop_count_reif(SimpleNode n) {
    gc.gen_jacop_count_reif(n);
  }

  /** Handles the jacop_count_var FlatZinc constraint. */
  public void jacop_count_var(SimpleNode n) {
    gc.gen_jacop_count_var(n);
  }

  /** Handles the jacop_count_var_reif FlatZinc constraint. */
  public void jacop_count_var_reif(SimpleNode n) {
    gc.gen_jacop_count_var_reif(n);
  }

  /** Handles the jacop_count_values FlatZinc constraint. */
  public void jacop_count_values(SimpleNode n) {
    gc.gen_jacop_count_values(n);
  }

  /** Handles the jacop_count_values_bounds FlatZinc constraint. */
  public void jacop_count_values_bounds(SimpleNode n) {
    gc.gen_jacop_count_values_bounds(n);
  }

  /** Handles the count_eq_imp FlatZinc constraint. */
  public void count_eq_imp(SimpleNode n) {
    gc.gen_count_eq_imp(n);
  }

  /** Handles the jacop_count_bounds FlatZinc constraint. */
  public void jacop_count_bounds(SimpleNode n) {
    gc.gen_jacop_count_bounds(n);
  }

  /** Handles the jacop_atleast FlatZinc constraint. */
  public void jacop_atleast(SimpleNode n) {
    gc.gen_jacop_atleast(n);
  }

  /** Handles the jacop_atleast_reif FlatZinc constraint. */
  public void jacop_atleast_reif(SimpleNode n) {
    gc.gen_jacop_atleast_reif(n);
  }

  /** Handles the jacop_atmost FlatZinc constraint. */
  public void jacop_atmost(SimpleNode n) {
    gc.gen_jacop_atmost(n);
  }

  /** Handles the jacop_atmost_reif FlatZinc constraint. */
  public void jacop_atmost_reif(SimpleNode n) {
    gc.gen_jacop_atmost_reif(n);
  }

  /** Handles the jacop_nvalue FlatZinc constraint. */
  public void jacop_nvalue(SimpleNode n) {
    gc.gen_jacop_nvalue(n);
  }

  /** Handles the jacop_minimum_arg_int FlatZinc constraint. */
  public void jacop_minimum_arg_int(SimpleNode n) {
    gc.gen_jacop_minimum_arg_int(n);
  }

  /** Handles the jacop_minimum_arg_bool FlatZinc constraint. */
  public void jacop_minimum_arg_bool(SimpleNode n) {
    gc.gen_jacop_minimum_arg_int(n);
  }

  /** Handles the jacop_minimum FlatZinc constraint. */
  public void jacop_minimum(SimpleNode n) {
    gc.gen_jacop_minimum(n);
  }

  /** Handles the jacop_maximum_arg_int FlatZinc constraint. */
  public void jacop_maximum_arg_int(SimpleNode n) {
    gc.gen_jacop_maximum_arg_int(n);
  }

  /** Handles the jacop_maximum_arg_bool FlatZinc constraint. */
  public void jacop_maximum_arg_bool(SimpleNode n) {
    gc.gen_jacop_maximum_arg_int(n);
  }

  /** Handles the jacop_maximum FlatZinc constraint. */
  public void jacop_maximum(SimpleNode n) {
    gc.gen_jacop_maximum(n);
  }

  /** Handles the jacop_member_int FlatZinc constraint. */
  public void jacop_member_int(SimpleNode n) {
    gc.gen_jacop_member(n);
  }

  /** Handles the jacop_member_int_reif FlatZinc constraint. */
  public void jacop_member_int_reif(SimpleNode n) {
    gc.gen_jacop_member_reif(n);
  }

  /** Handles the jacop_member_bool FlatZinc constraint. */
  public void jacop_member_bool(SimpleNode n) {
    gc.gen_jacop_member(n);
  }

  /** Handles the jacop_member_bool_reif FlatZinc constraint. */
  public void jacop_member_bool_reif(SimpleNode n) {
    gc.gen_jacop_member_reif(n);
  }

  /** Handles the jacop_table_int FlatZinc constraint. */
  public void jacop_table_int(SimpleNode n) {
    gc.gen_jacop_table_int(n);
  }

  /** Handles the jacop_table_bool FlatZinc constraint. */
  public void jacop_table_bool(SimpleNode n) {
    gc.gen_jacop_table_int(n);
  }

  /** Handles the jacop_assignment FlatZinc constraint. */
  public void jacop_assignment(SimpleNode n) {
    gc.gen_jacop_assignment(n);
  }

  /** Handles the jacop_regular FlatZinc constraint. */
  public void jacop_regular(SimpleNode n) {
    gc.gen_jacop_regular(n);
  }

  /** Handles the jacop_regular_set FlatZinc constraint. */
  public void jacop_regular_set(SimpleNode n) {
    gc.gen_jacop_regular_set(n);
  }

  /** Handles the jacop_knapsack FlatZinc constraint. */
  public void jacop_knapsack(SimpleNode n) {
    gc.gen_jacop_knapsack(n);
  }

  /** Handles the jacop_sequence FlatZinc constraint. */
  public void jacop_sequence(SimpleNode n) {
    gc.gen_jacop_sequence(n);
  }

  /** Handles the jacop_stretch FlatZinc constraint. */
  public void jacop_stretch(SimpleNode n) {
    gc.gen_jacop_stretch(n);
  }

  /** Handles the jacop_disjoint FlatZinc constraint. */
  public void jacop_disjoint(SimpleNode n) {
    gc.gen_jacop_disjoint(n);
  }

  /** Handles the jacop_networkflow FlatZinc constraint. */
  public void jacop_networkflow(SimpleNode n) {
    gc.gen_jacop_networkflow(n);
  }

  /** Handles the jacop_lex_less_int FlatZinc constraint. */
  public void jacop_lex_less_int(SimpleNode n) {
    gc.gen_jacop_lex_less_int(n);
  }

  /** Handles the jacop_lex_less_bool FlatZinc constraint. */
  public void jacop_lex_less_bool(SimpleNode n) {
    gc.gen_jacop_lex_less_int(n);
  }

  /** Handles the jacop_lex_lesseq_int FlatZinc constraint. */
  public void jacop_lex_lesseq_int(SimpleNode n) {
    gc.gen_jacop_lex_lesseq_int(n);
  }

  /** Handles the jacop_lex_lesseq_bool FlatZinc constraint. */
  public void jacop_lex_lesseq_bool(SimpleNode n) {
    gc.gen_jacop_lex_lesseq_int(n);
  }

  /** Handles the jacop_increasing FlatZinc constraint. */
  public void jacop_increasing(SimpleNode n) {
    gc.gen_jacop_increasing(n, false);
  }

  /** Handles the jacop_decreasing FlatZinc constraint. */
  public void jacop_decreasing(SimpleNode n) {
    gc.gen_jacop_decreasing(n, false);
  }

  /** Handles the jacop_strictly_increasing FlatZinc constraint. */
  public void jacop_strictly_increasing(SimpleNode n) {
    gc.gen_jacop_increasing(n, true);
  }

  /** Handles the jacop_strictly_decreasing FlatZinc constraint. */
  public void jacop_strictly_decreasing(SimpleNode n) {
    gc.gen_jacop_decreasing(n, true);
  }

  /** Handles the jacop_value_precede_int FlatZinc constraint. */
  public void jacop_value_precede_int(SimpleNode n) {
    gc.gen_jacop_value_precede_int(n);
  }

  /** Handles the jacop_value_precede_chain_int FlatZinc constraint. */
  public void jacop_value_precede_chain_int(SimpleNode n) {
    gc.gen_jacop_value_precede_chain_int(n);
  }

  /** Handles the jacop_bin_packing FlatZinc constraint. */
  public void jacop_bin_packing(SimpleNode n) {
    gc.gen_jacop_bin_packing(n);
  }

  /** Handles the jacop_bin_packing_capacity FlatZinc constraint. */
  public void jacop_bin_packing_capacity(SimpleNode n) {
    gc.gen_jacop_bin_packing_capacity(n);
  }

  /** Handles the jacop_float_maximum FlatZinc constraint. */
  public void jacop_float_maximum(SimpleNode n) {
    gc.gen_jacop_float_maximum(n);
  }

  /** Handles the jacop_float_minimum FlatZinc constraint. */
  public void jacop_float_minimum(SimpleNode n) {
    gc.gen_jacop_float_minimum(n);
  }

  /** Handles the jacop_geost FlatZinc constraint. */
  public void jacop_geost(SimpleNode n) {
    gc.gen_jacop_geost(n);
  }

  /** Handles the jacop_geost_bb FlatZinc constraint. */
  public void jacop_geost_bb(SimpleNode n) {
    gc.gen_jacop_geost_bb(n);
  }

  // if-then-else constraints
  /** Handles the jacop_if_then_else_int FlatZinc constraint. */
  public void jacop_if_then_else_int(SimpleNode n) {
    gc.gen_jacop_if_then_else_int(n);
  }

  /** Handles the jacop_if_then_else_bool FlatZinc constraint. */
  public void jacop_if_then_else_bool(SimpleNode n) {
    gc.gen_jacop_if_then_else_bool(n);
  }

  /** Handles the jacop_if_then_else_float FlatZinc constraint. */
  public void jacop_if_then_else_float(SimpleNode n) {
    gc.gen_jacop_if_then_else_float(n);
  }

  /** Handles the jacop_if_then_else_set FlatZinc constraint. */
  public void jacop_if_then_else_set(SimpleNode n) {
    gc.gen_jacop_if_then_else_set(n);
  }

  /** Handles the jacop_channel FlatZinc constraint. */
  public void jacop_channel(SimpleNode n) {
    gc.gen_jacop_channel(n);
  }

  /** Handles the jacop_all_equal_int FlatZinc constraint. */
  public void jacop_all_equal_int(SimpleNode n) {
    gc.gen_jacop_all_equal_int(n);
  }

  /** Handles the jacop_all_equal_int_reif FlatZinc constraint. */
  public void jacop_all_equal_int_reif(SimpleNode n) {
    gc.gen_jacop_all_equal_int_reif(n);
  }

  /** Handles the jacop_seq_precede_chain_int FlatZinc constraint. */
  public void jacop_seq_precede_chain_int(SimpleNode n) {
    gc.gen_jacop_seq_precede_chain_int(n);
  }

  // =========== optional constraints ===========

  /** Handles the jacop_cumulative_optional FlatZinc constraint. */
  public void jacop_cumulative_optional(SimpleNode n) {
    gc.gen_jacop_cumulative_optional(n);
  }

  /** Handles the jacop_disjunctive_optional FlatZinc constraint. */
  public void jacop_disjunctive_optional(SimpleNode n) {
    gc.gen_jacop_disjunctive_optional(n);
  }

  /** Handles the jacop_disjunctive_strict_optional FlatZinc constraint. */
  public void jacop_disjunctive_strict_optional(SimpleNode n) {
    gc.gen_jacop_disjunctive_strict_optional(n);
  }

  // Set constrints
  /** Handles the set_card FlatZinc constraint. */
  public void set_card(SimpleNode n) {
    sc.gen_set_card(n);
  }

  /** Handles the set_diff FlatZinc constraint. */
  public void set_diff(SimpleNode n) {
    sc.gen_set_diff(n);
  }

  /** Handles the set_eq FlatZinc constraint. */
  public void set_eq(SimpleNode n) {
    sc.gen_set_eq(n);
  }

  /** Handles the set_eq_reif FlatZinc constraint. */
  public void set_eq_reif(SimpleNode n) {
    sc.gen_set_eq_reif(n);
  }

  /** Handles the set_in FlatZinc constraint. */
  public void set_in(SimpleNode n) {
    sc.gen_set_in(n);
  }

  /** Handles the set_in_reif FlatZinc constraint. */
  public void set_in_reif(SimpleNode n) {
    sc.gen_set_in_reif(n);
  }

  /** Handles the set_in_imp FlatZinc constraint. */
  public void set_in_imp(SimpleNode n) {
    sc.gen_set_in_imp(n);
  }

  /** Handles the set_intersect FlatZinc constraint. */
  public void set_intersect(SimpleNode n) {
    sc.gen_set_intersect(n);
  }

  /** Handles the set_le FlatZinc constraint. */
  public void set_le(SimpleNode n) {
    sc.gen_set_le(n);
  }

  /** Handles the set_le_reif FlatZinc constraint. */
  public void set_le_reif(SimpleNode n) {
    sc.gen_set_le_reif(n);
  }

  /** Handles the set_lt FlatZinc constraint. */
  public void set_lt(SimpleNode n) {
    sc.gen_set_lt(n);
  }

  /** Handles the set_lt_reif FlatZinc constraint. */
  public void set_lt_reif(SimpleNode n) {
    sc.gen_set_lt_reif(n);
  }

  /** Handles the set_ne FlatZinc constraint. */
  public void set_ne(SimpleNode n) {
    sc.gen_set_ne(n);
  }

  /** Handles the set_ne_reif FlatZinc constraint. */
  public void set_ne_reif(SimpleNode n) {
    sc.gen_set_ne_reif(n);
  }

  /** Handles the set_subset FlatZinc constraint. */
  public void set_subset(SimpleNode n) {
    sc.gen_set_subset(n);
  }

  /** Handles the set_subset_reif FlatZinc constraint. */
  public void set_subset_reif(SimpleNode n) {
    sc.gen_set_subset_reif(n);
  }

  /** Handles the set_symdiff FlatZinc constraint. */
  public void set_symdiff(SimpleNode n) {
    sc.gen_set_symdiff(n);
  }

  /** Handles the set_union FlatZinc constraint. */
  public void set_union(SimpleNode n) {
    sc.gen_set_union(n);
  }

  /** Handles the jacop_int_set_channel FlatZinc constraint. */
  public void jacop_int_set_channel(SimpleNode n) {
    sc.gen_int_set_channel(n);
  }

  /** Handles the jacop_link_set_to_booleans FlatZinc constraint. */
  public void jacop_link_set_to_booleans(SimpleNode n) {
    sc.gen_link_set_to_booleans(n);
  }

  /** Handles the jacop_partition_set FlatZinc constraint. */
  public void jacop_partition_set(SimpleNode n) {
    sc.gen_partition_set(n);
  }

  // Floating-point comparisons
  /** Handles the float_eq FlatZinc constraint. */
  public void float_eq(SimpleNode n) {
    fcc.gen_float_eq(n);
  }

  /** Handles the float_eq_reif FlatZinc constraint. */
  public void float_eq_reif(SimpleNode n) {
    fcc.gen_float_eq_reif(n);
  }

  /** Handles the float_ne FlatZinc constraint. */
  public void float_ne(SimpleNode n) {
    fcc.gen_float_ne(n);
  }

  /** Handles the float_ne_reif FlatZinc constraint. */
  public void float_ne_reif(SimpleNode n) {
    fcc.gen_float_ne_reif(n);
  }

  /** Handles the float_le FlatZinc constraint. */
  public void float_le(SimpleNode n) {
    fcc.gen_float_le(n);
  }

  /** Handles the float_le_reif FlatZinc constraint. */
  public void float_le_reif(SimpleNode n) {
    fcc.gen_float_le_reif(n);
  }

  /** Handles the float_lt FlatZinc constraint. */
  public void float_lt(SimpleNode n) {
    fcc.gen_float_lt(n);
  }

  /** Handles the float_lt_reif FlatZinc constraint. */
  public void float_lt_reif(SimpleNode n) {
    fcc.gen_float_lt_reif(n);
  }

  // Floating-point linear constraint
  /** Handles the float_lin_eq FlatZinc constraint. */
  public void float_lin_eq(SimpleNode n) {
    flc.gen_float_lin_eq(n);
  }

  /** Handles the float_lin_eq_reif FlatZinc constraint. */
  public void float_lin_eq_reif(SimpleNode n) {
    flc.gen_float_lin_eq_reif(n);
  }

  /** Handles the float_lin_le FlatZinc constraint. */
  public void float_lin_le(SimpleNode n) {
    flc.gen_float_lin_le(n);
  }

  /** Handles the float_lin_le_reif FlatZinc constraint. */
  public void float_lin_le_reif(SimpleNode n) {
    flc.gen_float_lin_le_reif(n);
  }

  /** Handles the float_lin_lt FlatZinc constraint. */
  public void float_lin_lt(SimpleNode n) {
    flc.gen_float_lin_lt(n);
  }

  /** Handles the float_lin_lt_reif FlatZinc constraint. */
  public void float_lin_lt_reif(SimpleNode n) {
    flc.gen_float_lin_lt_reif(n);
  }

  /** Handles the float_lin_ne FlatZinc constraint. */
  public void float_lin_ne(SimpleNode n) {
    flc.gen_float_lin_ne(n);
  }

  /** Handles the float_lin_ne_reif FlatZinc constraint. */
  public void float_lin_ne_reif(SimpleNode n) {
    flc.gen_float_lin_ne_reif(n);
  }

  // Floating-point operations
  /** Handles the float_abs FlatZinc constraint. */
  public void float_abs(SimpleNode n) {
    foc.gen_float_abs(n);
  }

  /** Handles the float_acos FlatZinc constraint. */
  public void float_acos(SimpleNode n) {
    foc.gen_float_acos(n);
  }

  /** Handles the float_asin FlatZinc constraint. */
  public void float_asin(SimpleNode n) {
    foc.gen_float_asin(n);
  }

  /** Handles the float_atan FlatZinc constraint. */
  public void float_atan(SimpleNode n) {
    foc.gen_float_atan(n);
  }

  /** Handles the float_cos FlatZinc constraint. */
  public void float_cos(SimpleNode n) {
    foc.gen_float_cos(n);
  }

  /** Handles the float_exp FlatZinc constraint. */
  public void float_exp(SimpleNode n) {
    foc.gen_float_exp(n);
  }

  /** Handles the float_ln FlatZinc constraint. */
  public void float_ln(SimpleNode n) {
    foc.gen_float_ln(n);
  }

  /** Handles the float_log10 FlatZinc constraint. */
  public void float_log10(SimpleNode n) {
    foc.gen_float_log10(n);
  }

  /** Handles the float_log2 FlatZinc constraint. */
  public void float_log2(SimpleNode n) {
    foc.gen_float_log2(n);
  }

  /** Handles the float_sqrt FlatZinc constraint. */
  public void float_sqrt(SimpleNode n) {
    foc.gen_float_sqrt(n);
  }

  /** Handles the float_sin FlatZinc constraint. */
  public void float_sin(SimpleNode n) {
    foc.gen_float_sin(n);
  }

  /** Handles the float_tan FlatZinc constraint. */
  public void float_tan(SimpleNode n) {
    foc.gen_float_tan(n);
  }

  /** Handles the float_max FlatZinc constraint. */
  public void float_max(SimpleNode n) {
    foc.gen_float_max(n);
  }

  /** Handles the float_min FlatZinc constraint. */
  public void float_min(SimpleNode n) {
    foc.gen_float_min(n);
  }

  /** Handles the float_plus FlatZinc constraint. */
  public void float_plus(SimpleNode n) {
    foc.gen_float_plus(n);
  }

  /** Handles the float_times FlatZinc constraint. */
  public void float_times(SimpleNode n) {
    foc.gen_float_times(n);
  }

  /** Handles the float_div FlatZinc constraint. */
  public void float_div(SimpleNode n) {
    foc.gen_float_div(n);
  }

  /** Handles the float_pow FlatZinc constraint. */
  public void float_pow(SimpleNode n) {
    foc.gen_float_pow(n);
  }

  /** Handles the float_round FlatZinc constraint. */
  public void float_round(SimpleNode n) {
    foc.gen_float_round(n);
  }

  /** Handles the float_floor FlatZinc constraint. */
  public void float_floor(SimpleNode n) {
    foc.gen_float_floor(n);
  }

  /** Handles the float_ceil FlatZinc constraint. */
  public void float_ceil(SimpleNode n) {
    foc.gen_float_ceil(n);
  }

  // =========== graph constraints ===========

  /** Handles the jacop_graph_match FlatZinc constraint. */
  public void jacop_graph_match(SimpleNode n) {
    graph.gen_jacop_graph_match(n);
  }

  /** Handles the jacop_digraph_match FlatZinc constraint. */
  public void jacop_digraph_match(SimpleNode n) {
    graph.gen_jacop_digraph_match(n);
  }

  /** Handles the jacop_sub_graph_match FlatZinc constraint. */
  public void jacop_sub_graph_match(SimpleNode n) {
    graph.gen_jacop_sub_graph_match(n);
  }

  /** Handles the jacop_sub_digraph_match FlatZinc constraint. */
  public void jacop_sub_digraph_match(SimpleNode n) {
    graph.gen_jacop_sub_digraph_match(n);
  }

  /** Handles the jacop_clique FlatZinc constraint. */
  public void jacop_clique(SimpleNode n) {
    graph.gen_jacop_clique(n);
  }

  /** Handles the jacop_graph_isomorphism FlatZinc constraint. */
  public void jacop_graph_isomorphism(SimpleNode n) {
    graph.gen_jacop_graph_isomorphism(n);
  }
}
