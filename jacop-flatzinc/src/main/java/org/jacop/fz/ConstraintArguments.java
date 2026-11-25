/*
 * ConstraintArguments.java
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

package org.jacop.fz;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.core.IntVar;

/**
 * Checks the arguments of a constraint item against the declaration of its predicate, before the
 * front end reads them: an identifier that the model does not declare, an argument of another type,
 * a call with another number of arguments, and arrays of different lengths where the predicate
 * pairs their elements are errors of the model. The generators and the passes of the front end read
 * the arguments as the declaration gives them, so such a model threw a ClassCastException or a
 * NullPointerException in some modes, or was solved as some other model.
 *
 * <p>The check is lenient where JaCoP reads a value of another type the same way: a Boolean where
 * an integer is expected, an integer 0 or 1 or a 0..1 variable where a Boolean is expected. A
 * constraint whose predicate is not in the table is checked for undeclared identifiers only.
 */
final class ConstraintArguments {

  private enum Base {
    INT,
    BOOL,
    FLOAT,
    SET
  }

  /** The declared type of a parameter of a predicate. */
  private record Type(boolean array, boolean var, Base base, char group) {

    static Type parse(String s) {
      String t = s.trim();
      char group = 0;
      int at = t.indexOf('@');
      if (at >= 0) {
        group = t.charAt(at + 1);
        t = t.substring(0, at);
      }
      boolean array = t.startsWith("[]");
      if (array) {
        t = t.substring(2);
      }
      boolean var = t.startsWith("var ");
      if (var) {
        t = t.substring(4);
      }
      Base base =
          switch (t) {
            case "int" -> Base.INT;
            case "bool" -> Base.BOOL;
            case "float" -> Base.FLOAT;
            case "set" -> Base.SET;
            default -> throw new IllegalStateException("type " + s);
          };
      return new Type(array, var, base, group);
    }

    @Override
    public String toString() {
      String b =
          switch (base) {
            case INT -> "int";
            case BOOL -> "bool";
            case FLOAT -> "float";
            case SET -> "set of int";
          };
      return (array ? "array of " : "") + (var ? "var " : "") + b;
    }
  }

  // the predicates of the FlatZinc built-ins and of the JaCoP library (mznlib), as they are
  // declared; @X marks arrays whose elements the predicate pairs, which have one length
  private static final String[] DECLARATIONS = {
    "array_bool_and: []var bool, var bool",
    "array_bool_or: []var bool, var bool",
    "array_bool_xor: []var bool",
    "array_bool_and_imp: []var bool, var bool",
    "array_bool_or_imp: []var bool, var bool",
    "array_bool_xor_imp: []var bool, var bool",
    "bool_and: var bool, var bool, var bool",
    "bool_or: var bool, var bool, var bool",
    "bool_xor: var bool, var bool, var bool",
    "bool_and_imp: var bool, var bool, var bool",
    "bool_or_imp: var bool, var bool, var bool",
    "bool_xor_imp: var bool, var bool, var bool",
    "bool_not: var bool, var bool",
    "bool_clause: []var bool, []var bool",
    "bool_clause_reif: []var bool, []var bool, var bool",
    "bool_clause_imp: []var bool, []var bool, var bool",
    "bool2int: var bool, var int",
    "bool_eq: var bool, var bool",
    "bool_ne: var bool, var bool",
    "bool_le: var bool, var bool",
    "bool_lt: var bool, var bool",
    "bool_eq_reif: var bool, var bool, var bool",
    "bool_ne_reif: var bool, var bool, var bool",
    "bool_le_reif: var bool, var bool, var bool",
    "bool_lt_reif: var bool, var bool, var bool",
    "bool_eq_imp: var bool, var bool, var bool",
    "bool_ne_imp: var bool, var bool, var bool",
    "bool_le_imp: var bool, var bool, var bool",
    "bool_lt_imp: var bool, var bool, var bool",
    "bool_gt_imp: var bool, var bool, var bool",
    "bool_ge_imp: var bool, var bool, var bool",
    "int_eq: var int, var int",
    "int_ne: var int, var int",
    "int_le: var int, var int",
    "int_lt: var int, var int",
    "int_eq_reif: var int, var int, var bool",
    "int_ne_reif: var int, var int, var bool",
    "int_le_reif: var int, var int, var bool",
    "int_lt_reif: var int, var int, var bool",
    "int_eq_imp: var int, var int, var bool",
    "int_ne_imp: var int, var int, var bool",
    "int_le_imp: var int, var int, var bool",
    "int_lt_imp: var int, var int, var bool",
    "int_gt_imp: var int, var int, var bool",
    "int_ge_imp: var int, var int, var bool",
    "bool_lin_eq: []int@A, []var bool@A, var int",
    "bool_lin_ne: []int@A, []var bool@A, var int",
    "bool_lin_lt: []int@A, []var bool@A, var int",
    "bool_lin_le: []int@A, []var bool@A, var int",
    "bool_lin_eq_reif: []int@A, []var bool@A, var int, var bool",
    "bool_lin_ne_reif: []int@A, []var bool@A, var int, var bool",
    "bool_lin_lt_reif: []int@A, []var bool@A, var int, var bool",
    "bool_lin_le_reif: []int@A, []var bool@A, var int, var bool",
    "int_lin_eq: []int@A, []var int@A, int",
    "int_lin_ne: []int@A, []var int@A, int",
    "int_lin_lt: []int@A, []var int@A, int",
    "int_lin_le: []int@A, []var int@A, int",
    "int_lin_eq_reif: []int@A, []var int@A, int, var bool",
    "int_lin_ne_reif: []int@A, []var int@A, int, var bool",
    "int_lin_lt_reif: []int@A, []var int@A, int, var bool",
    "int_lin_le_reif: []int@A, []var int@A, int, var bool",
    "int_lin_eq_imp: []int@A, []var int@A, int, var bool",
    "int_lin_ne_imp: []int@A, []var int@A, int, var bool",
    "int_lin_lt_imp: []int@A, []var int@A, int, var bool",
    "int_lin_le_imp: []int@A, []var int@A, int, var bool",
    "int_lin_gt_imp: []int@A, []var int@A, int, var bool",
    "int_lin_ge_imp: []int@A, []var int@A, int, var bool",
    "int_min: var int, var int, var int",
    "int_max: var int, var int, var int",
    "int_mod: var int, var int, var int",
    "int_div: var int, var int, var int",
    "int_times: var int, var int, var int",
    "int_plus: var int, var int, var int",
    "int_pow: var int, var int, var int",
    "int_abs: var int, var int",
    "int2float: var int, var float",
    "array_bool_element: var int, []bool, var bool",
    "array_var_bool_element: var int, []var bool, var bool",
    "array_int_element: var int, []int, var int",
    "array_var_int_element: var int, []var int, var int",
    "array_set_element: var int, []set, var set",
    "array_var_set_element: var int, []var set, var set",
    "array_float_element: var int, []float, var float",
    "array_var_float_element: var int, []var float, var float",
    "set_card: var set, var int",
    "set_diff: var set, var set, var set",
    "set_intersect: var set, var set, var set",
    "set_union: var set, var set, var set",
    "set_symdiff: var set, var set, var set",
    "set_eq: var set, var set",
    "set_ne: var set, var set",
    "set_le: var set, var set",
    "set_lt: var set, var set",
    "set_subset: var set, var set",
    "set_superset: var set, var set",
    "set_eq_reif: var set, var set, var bool",
    "set_ne_reif: var set, var set, var bool",
    "set_le_reif: var set, var set, var bool",
    "set_lt_reif: var set, var set, var bool",
    "set_subset_reif: var set, var set, var bool",
    "set_superset_reif: var set, var set, var bool",
    "set_in: var int, var set",
    "set_in_reif: var int, var set, var bool",
    "set_in_imp: var int, var set, var bool",
    "float_eq: var float, var float",
    "float_ne: var float, var float",
    "float_le: var float, var float",
    "float_lt: var float, var float",
    "float_eq_reif: var float, var float, var bool",
    "float_ne_reif: var float, var float, var bool",
    "float_le_reif: var float, var float, var bool",
    "float_lt_reif: var float, var float, var bool",
    "float_lin_eq: []float@A, []var float@A, float",
    "float_lin_ne: []float@A, []var float@A, float",
    "float_lin_le: []float@A, []var float@A, float",
    "float_lin_lt: []float@A, []var float@A, float",
    "float_lin_eq_reif: []float@A, []var float@A, float, var bool",
    "float_lin_ne_reif: []float@A, []var float@A, float, var bool",
    "float_lin_le_reif: []float@A, []var float@A, float, var bool",
    "float_lin_lt_reif: []float@A, []var float@A, float, var bool",
    "float_abs: var float, var float",
    "float_acos: var float, var float",
    "float_asin: var float, var float",
    "float_atan: var float, var float",
    "float_cos: var float, var float",
    "float_sin: var float, var float",
    "float_tan: var float, var float",
    "float_cosh: var float, var float",
    "float_sinh: var float, var float",
    "float_tanh: var float, var float",
    "float_acosh: var float, var float",
    "float_asinh: var float, var float",
    "float_atanh: var float, var float",
    "float_exp: var float, var float",
    "float_ln: var float, var float",
    "float_log10: var float, var float",
    "float_log2: var float, var float",
    "float_sqrt: var float, var float",
    "float_max: var float, var float, var float",
    "float_min: var float, var float, var float",
    "float_plus: var float, var float, var float",
    "float_times: var float, var float, var float",
    "float_div: var float, var float, var float",
    "float_pow: var float, var float, var float",
    "float_round: var float, var int",
    "float_floor: var float, var int",
    "float_ceil: var float, var int",
    "jacop_cumulative: []var int@A, []var int@A, []var int@A, var int",
    "jacop_circuit: []var int",
    "jacop_circuit_offset: []var int, int",
    "jacop_subcircuit: []var int",
    "jacop_subcircuit_cost: []var int, []int, var int",
    "jacop_weighted_subcircuits: []var int, []var int, []int, []var int, var int, int",
    "jacop_alldiff: []var int",
    "jacop_softalldiff: []var int, var int, bool",
    "jacop_softgcc: []var int, []int, []var int, []var int, var int",
    "jacop_softgcc_var: []var int, []int, []var int, []var int, var int",
    "jacop_same: []var int, []var int",
    "jacop_used_by: []var int, []var int",
    "jacop_symmetric_gcc: []var int, int, []var int, []var int",
    "jacop_cardinality_matrix: []var int, int, []int, []var int, []var int",
    "jacop_stocking_cost: []var int, []int, []int, var int, int",
    "jacop_alldistinct: []var int",
    "jacop_alldifferent_except_0: []var int",
    "jacop_alldifferent_except: []var int, set",
    "jacop_among_var: []var int, []var int, var int",
    "jacop_among: []var int, set, var int",
    "jacop_gcc: []var int, []var int, int",
    "jacop_diff2_strict: []var int@A, []var int@A, []var int@A, []var int@A",
    "jacop_diffn_k: []var int@A, []var int@A, int, bool",
    "jacop_diff2: []var int",
    "jacop_list_diff2: []var int@A, []var int@A, []var int@A, []var int@A",
    "jacop_count: []var int, int, var int",
    "jacop_count_bounds: []var int, int, int, int",
    "count_eq_imp: []var int, var int, var int, var bool",
    "jacop_global_cardinality_closed: []var int, []int@A, []var int@A",
    "jacop_global_cardinality_low_up_closed: []var int, []int@A, []int@A, []int@A",
    "jacop_count_reif: []var int, int, var int, var bool",
    "jacop_count_var: []var int, var int, var int",
    "jacop_count_var_le: []var int, var int, var int, int",
    "jacop_count_var_ge: []var int, var int, var int, int",
    "jacop_regular_nfa: []var int, int, set, []set, int, set, int, int, int",
    "jacop_alldifferent_opt: []var int@A, []var bool@A",
    "jacop_sum_set: []int@A, []int@A, var set, var int",
    "jacop_array_var_int_element_nonshifted: var int, []var int, var int, int",
    "jacop_array_var_bool_element_nonshifted: var int, []var bool, var bool, int",
    "jacop_count_var_reif: []var int, var int, var int, var bool",
    "jacop_count_values: []var int, []int@A, []var int@A",
    "jacop_count_values_bounds: []var int, []int@A, []int@A, []int@A",
    "jacop_atleast: []var int, int, int",
    "jacop_atleast_reif: []var int, int, int, var bool",
    "jacop_atmost: []var int, int, int",
    "jacop_atmost_reif: []var int, int, int, var bool",
    "jacop_nvalue: var int, []var int",
    "jacop_minimum_arg_int: []var int, var int, int",
    "jacop_minimum_arg_bool: []var bool, var int, int",
    "jacop_minimum: var int, []var int",
    "jacop_maximum_arg_int: []var int, var int, int",
    "jacop_maximum_arg_bool: []var bool, var int, int",
    "jacop_maximum: var int, []var int",
    "jacop_member_int: []var int, var int",
    "jacop_member_int_reif: []var int, var int, var bool",
    "jacop_member_bool: []var bool, var int",
    "jacop_member_bool_reif: []var bool, var int, var bool",
    "jacop_table_int: []var int, []int",
    "jacop_table_bool: []var bool, []bool",
    "jacop_short_table_int: []var int, []int, int",
    "jacop_negative_table_int: []var int, []int",
    "jacop_table_int_reif: []var int, []int, var bool",
    "jacop_table_bool_reif: []var bool, []bool, var bool",
    "jacop_table_int_imp: []var int, []int, var bool",
    "jacop_table_bool_imp: []var bool, []bool, var bool",
    "jacop_assignment: []var int, []var int, int, int",
    "jacop_regular: []var int, int, int, []int, int, set, int",
    "jacop_cost_regular: []var int, int, int, []int, int, set, []int, var int",
    "jacop_cost_mdd: []var int, []int, []int@A, []set@A, []int@A, []int@A, var int",
    "jacop_chance_table: []var int, []int, []int, []int, []int, []int, []int, []int, var int",
    "jacop_prob_mdd: []var int, []int, []int, []int, []int, []int, []int, int, var int",
    "jacop_chance_sum: []var int, []int, []int, int, int, var int, int",
    "jacop_scenario_chance: []var int, []int, []int, []int, int, int, []var bool",
    "jacop_mdd: []var int, []int, []int@A, []set@A, []int@A",
    "jacop_regular_set: []var int, int, set, []int, int, set, int",
    "jacop_knapsack: []int@A, []int@A, var int, var int, []var int@A",
    "jacop_sequence: []var int, set, int, int, int",
    "jacop_deviation: []var int, int, int, int, var int",
    "jacop_reservoir: []var int@A, []int@A, int, int",
    "jacop_spread: []var int, int, int, int, var int",
    "jacop_stretch: []int@A, []int@A, []int@A, []var int",
    "jacop_disjoint: var set, var set",
    "jacop_networkflow: []int, []var int@A, []var int@A, []int, var int",
    "jacop_lex_less_int: []var int, []var int",
    "jacop_lex_less_bool: []var bool, []var bool",
    "jacop_lex_lesseq_int: []var int, []var int",
    "jacop_lex_lesseq_bool: []var bool, []var bool",
    "jacop_all_different_lists: []var int, int",
    "jacop_all_different_lists_except: []var int, int, []int",
    "jacop_lex_chain_less_int: []var int, int",
    "jacop_lex_chain_less_bool: []var bool, int",
    "jacop_lex_chain_lesseq_int: []var int, int",
    "jacop_lex_chain_lesseq_bool: []var bool, int",
    "jacop_increasing: []var int",
    "jacop_decreasing: []var int",
    "jacop_strictly_increasing: []var int",
    "jacop_strictly_decreasing: []var int",
    "jacop_value_precede_int: int, int, []var int",
    "jacop_value_precede_chain_int: []int, []var int",
    "jacop_bin_packing: []var int@A, []var int, []int@A, int",
    "jacop_bin_packing_capacity: []var int@A, []int, []int@A, int",
    "jacop_float_maximum: []var float, var float",
    "jacop_float_minimum: []var float, var float",
    "jacop_geost: int, []int, []int, []set, []var int, []var int",
    "jacop_geost_bb: int, []int, []int, []set, []var int, []var int, []int, []int",
    "jacop_if_then_else_int: []var bool@A, []var int@A, var int",
    "jacop_if_then_else_bool: []var bool@A, []var bool@A, var bool",
    "jacop_if_then_else_float: []var bool@A, []var float@A, var float",
    "jacop_if_then_else_set: []var bool@A, []var set@A, var set",
    "jacop_channel: var int, []var bool, set",
    "jacop_all_equal_int: []var int",
    "jacop_all_equal_int_reif: []var int, var bool",
    "jacop_seq_precede_chain_int: []var int",
    "jacop_inter_distance: []var int, int",
    "jacop_multi_inter_distance: []var int, int, int",
    "jacop_sort: []var int@A, []var int@A",
    "jacop_sort_permutation: []var int@A, []var int@A, []var int@A, int",
    "jacop_cumulative_optional: []var int@A, []var int@A, []var int@A, var int, []var bool@A",
    "jacop_cumulatives: []var int@A, []var int@A, []var int@A, []var int@A, []var int, bool, int",
    "jacop_cumulatives_optional: []var int@A, []var int@A, []var int@A, []var int@A, []var int,"
        + " bool, int, []var bool@A",
    "jacop_disjunctive_optional: []var int@A, []var int@A, []var bool@A",
    "jacop_disjunctive_setup: []var int@A, []var int@A, []int@A, []int",
    "jacop_disjunctive_setup_optional: []var int@A, []var int@A, []int@A, []int, []var bool@A",
    "jacop_disjunctive_strict_optional: []var int@A, []var int@A, []var bool@A",
    "jacop_alternative: var bool, var int, var int, []var bool@A, []var int@A, []var int@A",
    "jacop_span: var bool, var int, var int, []var bool@A, []var int@A, []var int@A",
    "jacop_int_set_channel: []var int, []var set, int, int",
    "jacop_link_set_to_booleans: var set, []var bool, int",
    "jacop_all_disjoint: []var set",
    "jacop_partition_set: []var set, set",
    "jacop_piecewise_linear: var float, var float, []float@A, []float@A",
    "jacop_graph_match: []int, []int, []int, []int, []var int, int",
    "jacop_digraph_match: []int, []int, []int, []int, []var int, int",
    "jacop_sub_graph_match: []int, []int, []int, []int, []var int, int",
    "jacop_sub_digraph_match: []int, []int, []int, []int, []var int, int",
    "jacop_clique: []int, []var bool, int",
    "jacop_graph_isomorphism: []set, []set, []int, []int, []var int, int",
    "jacop_reachable: []int@A, []int@A, var int, []var bool, []var bool@A, int",
    "jacop_dreachable: []int@A, []int@A, var int, []var bool, []var bool@A, int",
    "jacop_connected: []int@A, []int@A, []var bool, []var bool@A, int",
    "jacop_dconnected: []int@A, []int@A, []var bool, []var bool@A, int",
    "jacop_dag: []int@A, []int@A, []var bool, []var bool@A, int",
    "jacop_tree: []int@A, []int@A, var int, []var bool, []var bool@A, int",
    "jacop_dtree: []int@A, []int@A, var int, []var bool, []var bool@A, int",
    "jacop_path: []int@A, []int@A, var int, var int, []var bool, []var bool@A, int",
    "jacop_dpath: []int@A, []int@A, var int, var int, []var bool, []var bool@A, int",
    "jacop_bounded_path: []int@A, []int@A, []int@A, var int, var int, []var bool, []var bool@A,"
        + " var int, int",
    "jacop_bounded_dpath: []int@A, []int@A, []int@A, var int, var int, []var bool, []var bool@A,"
        + " var int, int",
    "jacop_steiner: []int@A, []int@A, []int@A, []var bool, []var bool@A, var int, int",
    "jacop_dsteiner: []int@A, []int@A, []int@A, var int, []var bool, []var bool@A, var int, int",
    "jacop_wst: int, []int@A, []int@A, []int@A, []var bool@A, var int",
    "jacop_dwst: int, []int@A, []int@A, []int@A, var int, []var bool@A, var int",
    "jacop_on_restart_status: var int",
    "jacop_on_restart_complete: var bool",
    "jacop_on_restart_sol_int: var int, var int",
    "jacop_on_restart_sol_float: var float, var float",
    "jacop_on_restart_sol_bool: var bool, var bool",
    "jacop_on_restart_last_val_int: var int, var int",
    "jacop_on_restart_last_val_float: var float, var float",
    "jacop_on_restart_last_val_bool: var bool, var bool",
    "jacop_on_restart_uniform_int: int, int, var int",
    "jacop_on_restart_uniform_float: float, float, var float",
  };

  private static final Map<String, Type[]> SIGNATURES = new HashMap<>();

  static {
    for (String d : DECLARATIONS) {
      int colon = d.indexOf(':');
      String[] params = d.substring(colon + 1).split(",");
      Type[] types = new Type[params.length];
      for (int i = 0; i < params.length; i++) {
        types[i] = Type.parse(params[i]);
      }
      SIGNATURES.put(d.substring(0, colon), types);
    }
  }

  private static final String END = "; execution aborted";

  private final Tables table;

  ConstraintArguments(Tables table) {
    this.table = table;
  }

  /**
   * Checks the arguments of one constraint item.
   *
   * @param constraintItem the constraint item, whose first child is the call
   * @throws IllegalArgumentException when the arguments do not fit the predicate
   */
  void check(SimpleNode constraintItem) {
    if (!(constraintItem.jjtGetChild(0) instanceof ASTConstElem call) || call.getName() == null) {
      return;
    }
    String name = call.getName();
    int n = call.jjtGetNumChildren();
    for (int i = 0; i < n; i++) {
      declared((SimpleNode) call.jjtGetChild(i));
    }
    Type[] types = SIGNATURES.get(name);
    if (types == null) {
      return;
    }
    if (types.length != n) {
      throw new IllegalArgumentException(
          "Constraint "
              + name
              + " has "
              + n
              + " arguments, its predicate takes "
              + types.length
              + END);
    }
    Map<Character, int[]> lengths = new HashMap<>();
    for (int i = 0; i < n; i++) {
      SimpleNode arg = (SimpleNode) call.jjtGetChild(i);
      Type t = types[i];
      int length = t.array() ? arrayLength(arg, t) : scalar(arg, t) ? 0 : -1;
      if (length < 0) {
        throw new IllegalArgumentException(
            "Argument " + (i + 1) + " of constraint " + name + " is not of type " + t + END);
      }
      if (t.group() != 0) {
        int[] first = lengths.putIfAbsent(t.group(), new int[] {length, i});
        if (first != null && first[0] != length) {
          throw new IllegalArgumentException(
              "Arguments "
                  + (first[1] + 1)
                  + " and "
                  + (i + 1)
                  + " of constraint "
                  + name
                  + " are arrays of different lengths"
                  + END);
        }
      }
    }
    dimensions(name, call);
  }

  // the arrays whose length the other arguments give: a transition table of states x symbols,
  // tuples of the length of the scope, edges between the nodes of a diagram
  private void dimensions(String name, SimpleNode call) {
    switch (name) {
      case "jacop_regular", "jacop_cost_regular" -> {
        long cells = (long) intArg(call, 1) * intArg(call, 2);
        int[] d = ints(call, 3);
        if (d.length != cells
            || "jacop_cost_regular".equals(name) && ints(call, 6).length != cells) {
          throw dimension(name, "a table of states x symbols has " + cells + " entries");
        }
      }
      case "jacop_diffn_k" -> {
        int k = intArg(call, 2);
        if (k < 1
            || arrayLength((SimpleNode) call.jjtGetChild(0), Type.parse("[]var int")) % k != 0) {
          throw dimension(name, "the origins are not boxes of " + k + " dimensions");
        }
      }
      case "jacop_table_int",
          "jacop_table_bool",
          "jacop_short_table_int",
          "jacop_negative_table_int",
          "jacop_table_int_reif",
          "jacop_table_bool_reif",
          "jacop_table_int_imp",
          "jacop_table_bool_imp" -> {
        int scope = arrayLength((SimpleNode) call.jjtGetChild(0), Type.parse("[]var int"));
        int tuples = arrayLength((SimpleNode) call.jjtGetChild(1), Type.parse("[]int"));
        if (scope > 0 ? tuples % scope != 0 : tuples != 0) {
          throw dimension(name, "the tuples are not of the length of the scope, " + scope);
        }
      }
      case "jacop_networkflow" -> {
        int arcs = ints(call, 0).length;
        if (arcs != 2 * arrayLength((SimpleNode) call.jjtGetChild(1), Type.parse("[]var int"))) {
          throw dimension(name, "the arcs are not one pair of nodes for each flow");
        }
      }
      case "jacop_mdd", "jacop_cost_mdd" -> {
        int nodes = ints(call, 1).length;
        int[] from = ints(call, 2);
        int[] to = ints(call, "jacop_mdd".equals(name) ? 4 : 5);
        for (int e = 0; e < from.length; e++) {
          if (from[e] < 1 || from[e] > nodes || to[e] < 0 || to[e] > nodes) {
            throw dimension(name, "an edge goes outside the nodes 1.." + nodes);
          }
        }
      }
      default -> {
        // no dimension to check
      }
    }
  }

  private static IllegalArgumentException dimension(String name, String what) {
    return new IllegalArgumentException(
        "The arguments of constraint " + name + " do not fit: " + what + END);
  }

  // the value of a par int argument, which the types checked already
  private int intArg(SimpleNode call, int i) {
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) call.jjtGetChild(i);
    return switch (e.getType()) {
      case 2 -> table.intTable.get(e.getIdent());
      case 3 -> table.intArrayTable.get(e.getIdent())[e.getInt()];
      default -> e.getInt();
    };
  }

  // the values of an array of par int argument, which the types checked already
  private int[] ints(SimpleNode call, int i) {
    SimpleNode arg = (SimpleNode) call.jjtGetChild(i);
    if (arg instanceof ASTScalarFlatExpr e) {
      return table.intArrayTable.get(e.getIdent());
    }
    int[] packed = arg.packedInts();
    if (packed != null) {
      return packed;
    }
    int[] values = new int[arg.jjtGetNumChildren()];
    for (int k = 0; k < values.length; k++) {
      values[k] = intArg(arg, k);
    }
    return values;
  }

  // every identifier of an argument names a symbol of the model, and every array access lies
  // within its array
  private void declared(SimpleNode node) {
    if (node instanceof ASTScalarFlatExpr e) {
      if (e.getType() == 2 && !table.isIdentifier(e.getIdent())) {
        throw undefined(e.getIdent());
      }
      if (e.getType() == 3) {
        int length = arrayLength(e.getIdent());
        if (length < 0) {
          throw undefined(e.getIdent());
        }
        if (e.getInt() < 0 || e.getInt() >= length) {
          throw new IllegalArgumentException(
              "Index out of bound for " + e.getIdent() + "[" + (e.getInt() + 1) + "]");
        }
      }
      return;
    }
    if (node.packedInts() != null) {
      return;
    }
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      declared((SimpleNode) node.jjtGetChild(i));
    }
  }

  private static IllegalArgumentException undefined(String ident) {
    return new IllegalArgumentException(
        "Symbol \"" + ident + "\" does not have assigned value when refered" + END);
  }

  private int arrayLength(String ident) {
    Object a = arrayOf(ident);
    return switch (a) {
      case int[] v -> v.length;
      case double[] v -> v.length;
      case Object[] v -> v.length;
      case null, default -> -1;
    };
  }

  private Object arrayOf(String ident) {
    if (table.variableArrayTable.containsKey(ident)) {
      return table.variableArrayTable.get(ident);
    } else if (table.intArrayTable.containsKey(ident)) {
      return table.intArrayTable.get(ident);
    } else if (table.floatArrayTable.containsKey(ident)) {
      return table.floatArrayTable.get(ident);
    } else if (table.variableFloatArrayTable.containsKey(ident)) {
      return table.variableFloatArrayTable.get(ident);
    } else if (table.setArrayTable.containsKey(ident)) {
      return table.setArrayTable.get(ident);
    } else if (table.setVariableArrayTable.containsKey(ident)) {
      return table.setVariableArrayTable.get(ident);
    }
    return null;
  }

  // the length of an array argument of the type, or -1 when it is not one
  private int arrayLength(SimpleNode arg, Type t) {
    Type element = new Type(false, t.var(), t.base(), (char) 0);
    if (arg instanceof ASTArrayLiteral) {
      int[] packed = arg.packedInts();
      if (packed != null) {
        for (int v : packed) {
          if (!intFits(v, element)) {
            return -1;
          }
        }
        return packed.length;
      }
      for (int i = 0; i < arg.jjtGetNumChildren(); i++) {
        if (!scalar((SimpleNode) arg.jjtGetChild(i), element)) {
          return -1;
        }
      }
      return arg.jjtGetNumChildren();
    }
    if (!(arg instanceof ASTScalarFlatExpr e) || e.getType() != 2) {
      return -1;
    }
    String ident = e.getIdent();
    boolean fits =
        switch (t.base()) {
          case INT ->
              table.intArrayTable.containsKey(ident)
                  || t.var() && table.variableArrayTable.containsKey(ident);
          case BOOL -> {
            int[] p = table.intArrayTable.get(ident);
            if (p != null) {
              yield allBool(p);
            }
            IntVar[] v = t.var() ? table.variableArrayTable.get(ident) : null;
            yield v != null && allBool(v);
          }
          case FLOAT ->
              table.floatArrayTable.containsKey(ident)
                  || t.var() && table.variableFloatArrayTable.containsKey(ident);
          case SET ->
              table.setArrayTable.containsKey(ident)
                  || t.var() && table.setVariableArrayTable.containsKey(ident);
        };
    return fits ? arrayLength(ident) : -1;
  }

  private static boolean allBool(int[] p) {
    for (int v : p) {
      if (v < 0 || v > 1) {
        return false;
      }
    }
    return true;
  }

  private static boolean allBool(IntVar[] v) {
    for (IntVar x : v) {
      if (!bool(x)) {
        return false;
      }
    }
    return true;
  }

  private static boolean bool(IntVar x) {
    return x != null && x.min() >= 0 && x.max() <= 1;
  }

  private static boolean intFits(int v, Type t) {
    return t.base() == Base.INT || t.base() == Base.BOOL && v >= 0 && v <= 1;
  }

  // whether a scalar argument (or an element of an array literal) is of the type
  private boolean scalar(SimpleNode arg, Type t) {
    if (arg instanceof ASTSetLiteral) {
      return t.base() == Base.SET;
    }
    if (!(arg instanceof ASTScalarFlatExpr e)) {
      return false;
    }
    return switch (e.getType()) {
      case 0, 1 -> intFits(e.getInt(), t);
      case 5 -> t.base() == Base.FLOAT;
      case 2 -> identifier(e.getIdent(), t);
      case 3 -> element(e.getIdent(), e.getInt(), t);
      default -> false;
    };
  }

  private boolean identifier(String ident, Type t) {
    return switch (t.base()) {
      case INT ->
          table.intTable.containsKey(ident) || t.var() && table.variableTable.containsKey(ident);
      case BOOL -> {
        Integer p = table.intTable.get(ident);
        if (p != null) {
          yield p >= 0 && p <= 1;
        }
        yield t.var() && bool(table.variableTable.get(ident));
      }
      case FLOAT ->
          table.floatTable.containsKey(ident)
              || t.var() && table.variableFloatTable.containsKey(ident);
      case SET ->
          table.setTable.containsKey(ident) || t.var() && table.setVariableTable.containsKey(ident);
    };
  }

  // an element a[i] of a declared array; i lies within it (declared checks it first)
  private boolean element(String ident, int i, Type t) {
    Object a = arrayOf(ident);
    return switch (t.base()) {
      case INT -> a instanceof int[] || t.var() && a instanceof IntVar[];
      case BOOL ->
          a instanceof int[] p
              ? p[i] >= 0 && p[i] <= 1
              : t.var() && a instanceof IntVar[] v && bool(v[i]);
      case FLOAT ->
          a instanceof double[] || t.var() && table.variableFloatArrayTable.containsKey(ident);
      case SET ->
          table.setArrayTable.containsKey(ident)
              || t.var() && table.setVariableArrayTable.containsKey(ident);
    };
  }

  /**
   * The names of the predicates whose arguments are checked, for tests.
   *
   * @return the names
   */
  static List<String> predicates() {
    return new ArrayList<>(SIGNATURES.keySet());
  }
}
