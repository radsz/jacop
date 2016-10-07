/**
 *  ConstraintFncs.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
package org.jacop.fz.constraints;

import java.util.*;
import java.util.function.*;

import org.jacop.fz.*;

public final class ConstraintFncs {

  // Boolean constraints
  public static void array_bool_and(SimpleNode n) {BoolConstraints.gen_array_bool_and(n);}
  public static void array_bool_or(SimpleNode n) {BoolConstraints.gen_array_bool_or(n);}
  public static void array_bool_xor(SimpleNode n) {BoolConstraints.gen_array_bool_xor(n);}
  public static void bool_and(SimpleNode n) {BoolConstraints.gen_bool_and(n);}
  public static void bool_not(SimpleNode n) {BoolConstraints.gen_bool_not(n);}
  public static void bool_or(SimpleNode n) {BoolConstraints.gen_bool_or(n);}
  public static void bool_xor(SimpleNode n) {BoolConstraints.gen_bool_xor(n);}
  public static void bool_clause(SimpleNode n) {BoolConstraints.gen_bool_clause(n);}
  public static void bool_clause_reif(SimpleNode n) {BoolConstraints.gen_bool_clause_reif(n);}
  public static void bool2int(SimpleNode n) {BoolConstraints.gen_bool2int(n);}

  // Comparisons boolean and int
  public static void bool_eq(SimpleNode n) {ComparisonConstraints.gen_bool_eq(n);}
  public static void bool_eq_reif(SimpleNode n) {ComparisonConstraints.gen_bool_eq_reif(n);}
  public static void bool_ne(SimpleNode n) {ComparisonConstraints.gen_bool_ne(n);}
  public static void bool_ne_reif(SimpleNode n) {ComparisonConstraints.gen_bool_ne_reif(n);}
  public static void bool_le(SimpleNode n) {ComparisonConstraints.gen_bool_le(n);}
  public static void bool_le_reif(SimpleNode n) {ComparisonConstraints.gen_bool_le_reif(n);}
  public static void bool_lt(SimpleNode n) {ComparisonConstraints.gen_bool_lt(n);}
  public static void bool_lt_reif(SimpleNode n) {ComparisonConstraints.gen_bool_lt_reif(n);}

  public static void int_eq(SimpleNode n) {ComparisonConstraints.gen_int_eq(n);}
  public static void int_eq_reif(SimpleNode n) {ComparisonConstraints.gen_int_eq_reif(n);}
  public static void int_ne(SimpleNode n) {ComparisonConstraints.gen_int_ne(n);}
  public static void int_ne_reif(SimpleNode n) {ComparisonConstraints.gen_int_ne_reif(n);}
  public static void int_le(SimpleNode n) {ComparisonConstraints.gen_int_le(n);}
  public static void int_le_reif(SimpleNode n) {ComparisonConstraints.gen_int_le_reif(n);}
  public static void int_lt(SimpleNode n) {ComparisonConstraints.gen_int_lt(n);}
  public static void int_lt_reif(SimpleNode n) {ComparisonConstraints.gen_int_lt_reif(n);}

  // Linear bool and int constraints
  public static void bool_lin_eq(SimpleNode n) {LinearConstraints.gen_bool_lin_eq(n);}
  public static void bool_lin_eq_reif(SimpleNode n) {LinearConstraints.gen_int_lin_eq_reif(n);}
  public static void bool_lin_ne(SimpleNode n) {LinearConstraints.gen_int_lin_ne(n);}
  public static void bool_lin_ne_reif(SimpleNode n) {LinearConstraints.gen_int_lin_ne_reif(n);}
  public static void bool_lin_lt(SimpleNode n) {LinearConstraints.gen_int_lin_lt(n);}
  public static void bool_lin_lt_reif(SimpleNode n) {LinearConstraints.gen_int_lin_lt_reif(n);}
  public static void bool_lin_le(SimpleNode n) {LinearConstraints.gen_int_lin_le(n);}
  public static void bool_lin_le_reif(SimpleNode n) {LinearConstraints.gen_int_lin_le_reif(n);}

  public static void int_lin_eq(SimpleNode n) {LinearConstraints.gen_int_lin_eq(n);}
  public static void int_lin_eq_reif(SimpleNode n) {LinearConstraints.gen_int_lin_eq_reif(n);}
  public static void int_lin_ne(SimpleNode n) {LinearConstraints.gen_int_lin_ne(n);}
  public static void int_lin_ne_reif(SimpleNode n) {LinearConstraints.gen_int_lin_ne_reif(n);}
  public static void int_lin_lt(SimpleNode n) {LinearConstraints.gen_int_lin_lt(n);}
  public static void int_lin_lt_reif(SimpleNode n) {LinearConstraints.gen_int_lin_lt_reif(n);}
  public static void int_lin_le(SimpleNode n) {LinearConstraints.gen_int_lin_le(n);}
  public static void int_lin_le_reif(SimpleNode n) {LinearConstraints.gen_int_lin_le_reif(n);}

  // Diverse int operations
  public static void int_min(SimpleNode n) {OperationConstraints.gen_int_min(n);}
  public static void int_max(SimpleNode n) {OperationConstraints.gen_int_max(n);}
  public static void int_mod(SimpleNode n) {OperationConstraints.gen_int_mod(n);}
  public static void int_div(SimpleNode n) {OperationConstraints.gen_int_div(n);}
  public static void int_abs(SimpleNode n) {OperationConstraints.gen_int_abs(n);}
  public static void int_times(SimpleNode n) {OperationConstraints.gen_int_times(n);}
  public static void int_plus(SimpleNode n) {OperationConstraints.gen_int_plus(n);}
  public static void int_pow(SimpleNode n) {OperationConstraints.gen_int_pow(n);}
  public static void int2float(SimpleNode n) {OperationConstraints.gen_int2float(n);}
  
  // Element int, boolean, set and float constraints
  public static void array_bool_element(SimpleNode n) {ElementConstraints.gen_array_int_element(n);}
  public static void array_var_bool_element(SimpleNode n) {ElementConstraints.gen_array_var_int_element(n);}
  public static void array_int_element(SimpleNode n) {ElementConstraints.gen_array_int_element(n);}
  public static void array_var_int_element(SimpleNode n) {ElementConstraints.gen_array_var_int_element(n);}
  public static void array_set_element(SimpleNode n) {ElementConstraints.gen_array_set_element(n);}
  public static void array_var_set_element(SimpleNode n) {ElementConstraints.gen_array_var_set_element(n);}
  public static void array_float_element(SimpleNode n) {ElementConstraints.gen_array_float_element(n);}
  
  // Global constraints
  public static void jacop_cumulative(SimpleNode n) {GlobalConstraints.gen_jacop_cumulative(n);}
  public static void jacop_circuit(SimpleNode n) {GlobalConstraints.gen_jacop_circuit(n);}
  public static void jacop_subcircuit(SimpleNode n) {GlobalConstraints.gen_jacop_subcircuit(n);}
  public static void jacop_alldiff(SimpleNode n) {GlobalConstraints.gen_jacop_alldiff(n);}
  public static void jacop_softalldiff(SimpleNode n) {GlobalConstraints.gen_jacop_softalldiff(n);}
  public static void jacop_softgcc(SimpleNode n) {GlobalConstraints.gen_jacop_softgcc(n);}
  public static void jacop_alldistinct(SimpleNode n) {GlobalConstraints.gen_jacop_alldistinct(n);}
  public static void jacop_among_var(SimpleNode n) {GlobalConstraints.gen_jacop_among_var(n);}
  public static void jacop_among(SimpleNode n) {GlobalConstraints.gen_jacop_among(n);}
  public static void jacop_gcc(SimpleNode n) {GlobalConstraints.gen_jacop_gcc(n);}
  public static void jacop_global_cardinality_closed(SimpleNode n) {GlobalConstraints.gen_jacop_global_cardinality_closed(n);}
  public static void jacop_global_cardinality_low_up_closed(SimpleNode n) {GlobalConstraints.gen_jacop_global_cardinality_low_up_closed(n);}
  public static void jacop_diff2_strict(SimpleNode n) {GlobalConstraints.gen_jacop_diff2_strict(n);}
  public static void jacop_diff2(SimpleNode n) {GlobalConstraints.gen_jacop_diff2(n);}
  public static void jacop_list_diff2(SimpleNode n) {GlobalConstraints.gen_jacop_list_diff2(n);}
  public static void jacop_count(SimpleNode n) {GlobalConstraints.gen_jacop_count(n);}
  public static void jacop_nvalue(SimpleNode n) {GlobalConstraints.gen_jacop_nvalue(n);}
  public static void jacop_minimum_arg_int(SimpleNode n) {GlobalConstraints.gen_jacop_minimum_arg_int(n);}
  public static void jacop_minimum(SimpleNode n) {GlobalConstraints.gen_jacop_minimum(n);}
  public static void jacop_maximum_arg_int(SimpleNode n) {GlobalConstraints.gen_jacop_maximum_arg_int(n);}
  public static void jacop_maximum(SimpleNode n) {GlobalConstraints.gen_jacop_maximum(n);}
  public static void jacop_table_int(SimpleNode n) {GlobalConstraints.gen_jacop_table_int(n);}
  public static void jacop_table_bool(SimpleNode n) {GlobalConstraints.gen_jacop_table_int(n);}
  public static void jacop_assignment(SimpleNode n) {GlobalConstraints.gen_jacop_assignment(n);}
  public static void jacop_regular(SimpleNode n) {GlobalConstraints.gen_jacop_regular(n);}
  public static void jacop_knapsack(SimpleNode n) {GlobalConstraints.gen_jacop_knapsack(n);}
  public static void jacop_sequence(SimpleNode n) {GlobalConstraints.gen_jacop_sequence(n);}
  public static void jacop_stretch(SimpleNode n) {GlobalConstraints.gen_jacop_stretch(n);}
  public static void jacop_disjoint(SimpleNode n) {GlobalConstraints.gen_jacop_disjoint(n);}
  public static void jacop_networkflow(SimpleNode n) {GlobalConstraints.gen_jacop_networkflow(n);}
  public static void jacop_lex_less_int(SimpleNode n) {GlobalConstraints.gen_jacop_lex_less_int(n);}
  public static void jacop_lex_less_bool(SimpleNode n) {GlobalConstraints.gen_jacop_lex_less_int(n);}
  public static void jacop_lex_lesseq_int(SimpleNode n) {GlobalConstraints.gen_jacop_lex_lesseq_int(n);}
  public static void jacop_lex_lesseq_bool(SimpleNode n) {GlobalConstraints.gen_jacop_lex_lesseq_int(n);}
  public static void jacop_bin_packing(SimpleNode n) {GlobalConstraints.gen_jacop_bin_packing(n);}
  public static void jacop_float_maximum(SimpleNode n) {GlobalConstraints.gen_jacop_float_maximum(n);}
  public static void jacop_float_minimum(SimpleNode n) {GlobalConstraints.gen_jacop_float_minimum(n);}
  public static void jacop_geost(SimpleNode n) {GlobalConstraints.gen_jacop_geost(n);}
  public static void jacop_geost_bb(SimpleNode n) {GlobalConstraints.gen_jacop_geost_bb(n);}


  // Set constrints
  public static void set_card(SimpleNode n) {SetConstraints.gen_set_card(n);}
  public static void set_diff(SimpleNode n) {SetConstraints.gen_set_diff(n);}
  public static void set_eq(SimpleNode n) {SetConstraints.gen_set_eq(n);}
  public static void set_eq_reif(SimpleNode n) {SetConstraints.gen_set_eq_reif(n);}
  public static void set_in(SimpleNode n) {SetConstraints.gen_set_in(n);}
  public static void set_in_reif(SimpleNode n) {SetConstraints.gen_set_in_reif(n);}
  public static void set_intersect(SimpleNode n) {SetConstraints.gen_set_intersect(n);}
  public static void set_le(SimpleNode n) {SetConstraints.gen_set_le(n);}
  public static void set_lt(SimpleNode n) {SetConstraints.gen_set_lt(n);}
  public static void set_ne(SimpleNode n) {SetConstraints.gen_set_ne(n);}
  public static void set_ne_reif(SimpleNode n) {SetConstraints.gen_set_ne_reif(n);}
  public static void set_subset(SimpleNode n) {SetConstraints.gen_set_subset(n);}
  public static void set_subset_reif(SimpleNode n) {SetConstraints.gen_set_subset_reif(n);}
  public static void set_symdiff(SimpleNode n) {SetConstraints.gen_set_symdiff(n);}
  public static void set_union(SimpleNode n) {SetConstraints.gen_set_union(n);}

  // Floating-point comparisons
  public static void float_eq(SimpleNode n) {FloatComparisonConstraints.gen_float_eq(n);}
  public static void float_eq_reif(SimpleNode n) {FloatComparisonConstraints.gen_float_eq_reif(n);}
  public static void float_ne(SimpleNode n) {FloatComparisonConstraints.gen_float_ne(n);}
  public static void float_ne_reif(SimpleNode n) {FloatComparisonConstraints.gen_float_ne_reif(n);}
  public static void float_le(SimpleNode n) {FloatComparisonConstraints.gen_float_le(n);}
  public static void float_le_reif(SimpleNode n) {FloatComparisonConstraints.gen_float_le_reif(n);}
  public static void float_lt(SimpleNode n) {FloatComparisonConstraints.gen_float_lt(n);}
  public static void float_lt_reif(SimpleNode n) {FloatComparisonConstraints.gen_float_lt_reif(n);}

  // Floating-point linear constraint
  public static void float_lin_eq(SimpleNode n) {FloatLinearConstraints.gen_float_lin_eq(n);}
  public static void float_lin_eq_reif(SimpleNode n) {FloatLinearConstraints.gen_float_lin_eq_reif(n);}
  public static void float_lin_le(SimpleNode n) {FloatLinearConstraints.gen_float_lin_le(n);}
  public static void float_lin_le_reif(SimpleNode n) {FloatLinearConstraints.gen_float_lin_le_reif(n);}
  public static void float_lin_lt(SimpleNode n) {FloatLinearConstraints.gen_float_lin_lt(n);}
  public static void float_lin_lt_reif(SimpleNode n) {FloatLinearConstraints.gen_float_lin_lt_reif(n);}
  public static void float_lin_ne(SimpleNode n) {FloatLinearConstraints.gen_float_lin_ne(n);}
  public static void float_lin_ne_reif(SimpleNode n) {FloatLinearConstraints.gen_float_lin_ne_reif(n);}

  // Floating-point operations
  public static void float_abs(SimpleNode n) {FloatOperationConstraints.gen_float_abs(n);}
  public static void float_acos(SimpleNode n) {FloatOperationConstraints.gen_float_acos(n);}
  public static void float_asin(SimpleNode n) {FloatOperationConstraints.gen_float_asin(n);}
  public static void float_atan(SimpleNode n) {FloatOperationConstraints.gen_float_atan(n);}
  public static void float_cos(SimpleNode n) {FloatOperationConstraints.gen_float_cos(n);}
  public static void float_exp(SimpleNode n) {FloatOperationConstraints.gen_float_exp(n);}
  public static void float_ln(SimpleNode n) {FloatOperationConstraints.gen_float_ln(n);}
  public static void float_log10(SimpleNode n) {FloatOperationConstraints.gen_float_log10(n);}
  public static void float_log2(SimpleNode n) {FloatOperationConstraints.gen_float_log2(n);}
  public static void float_sqrt(SimpleNode n) {FloatOperationConstraints.gen_float_sqrt(n);}
  public static void float_sin(SimpleNode n) {FloatOperationConstraints.gen_float_sin(n);}
  public static void float_tan(SimpleNode n) {FloatOperationConstraints.gen_float_tan(n);}
  public static void float_max(SimpleNode n) {FloatOperationConstraints.gen_float_max(n);}
  public static void float_min(SimpleNode n) {FloatOperationConstraints.gen_float_min(n);}
  public static void float_plus(SimpleNode n) {FloatOperationConstraints.gen_float_plus(n);}
  public static void float_times(SimpleNode n) {FloatOperationConstraints.gen_float_times(n);}
  public static void float_div(SimpleNode n) {FloatOperationConstraints.gen_float_div(n);}
  public static void float_pow(SimpleNode n) {FloatOperationConstraints.gen_float_pow(n);}

  // public static void float_cosh(SimpleNode n) {FloatOperationConstraints.gen_float_cosh(n);}
  // public static void float_sinh(SimpleNode n) {FloatOperationConstraints.gen_float_sinh(n);}
  // public static void float_tanh(SimpleNode n) {FloatOperationConstraints.gen_float_tanh(n);}

}
