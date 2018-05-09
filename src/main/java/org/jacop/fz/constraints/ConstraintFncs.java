/**
 * ConstraintFncs.java
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

import org.jacop.fz.*;

public final class ConstraintFncs {

    BoolConstraints bc;
    ComparisonConstraints cc;
    LinearConstraints lc;
    OperationConstraints oc;
    ElementConstraints ec;
    GlobalConstraints gc;
    SetConstraints sc;
    FloatComparisonConstraints fcc;
    FloatLinearConstraints flc;
    FloatOperationConstraints foc;

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
    }
    
    // Boolean constraints
    public void array_bool_and(SimpleNode n) {
        bc.gen_array_bool_and(n);
    }

    public void array_bool_or(SimpleNode n) {
        bc.gen_array_bool_or(n);
    }

    public void array_bool_xor(SimpleNode n) {
        bc.gen_array_bool_xor(n);
    }

    public void bool_and(SimpleNode n) {
        bc.gen_bool_and(n);
    }

    public void bool_not(SimpleNode n) {
        bc.gen_bool_not(n);
    }

    public void bool_or(SimpleNode n) {
        bc.gen_bool_or(n);
    }

    public void bool_xor(SimpleNode n) {
        bc.gen_bool_xor(n);
    }

    public void bool_clause(SimpleNode n) {
        bc.gen_bool_clause(n);
    }

    public void bool_clause_reif(SimpleNode n) {
        bc.gen_bool_clause_reif(n);
    }

    public void bool2int(SimpleNode n) {
        bc.gen_bool2int(n);
    }

    // Comparisons boolean and int
    public void bool_eq(SimpleNode n) {
        cc.gen_bool_eq(n);
    }

    public void bool_eq_reif(SimpleNode n) {
        cc.gen_bool_eq_reif(n);
    }

    public void bool_ne(SimpleNode n) {
        cc.gen_bool_ne(n);
    }

    public void bool_ne_reif(SimpleNode n) {
        cc.gen_bool_ne_reif(n);
    }

    public void bool_le(SimpleNode n) {
        cc.gen_bool_le(n);
    }

    public void bool_le_reif(SimpleNode n) {
        cc.gen_bool_le_reif(n);
    }

    public void bool_lt(SimpleNode n) {
        cc.gen_bool_lt(n);
    }

    public void bool_lt_reif(SimpleNode n) {
        cc.gen_bool_lt_reif(n);
    }

    public void int_eq(SimpleNode n) {
        cc.gen_int_eq(n);
    }

    public void int_eq_reif(SimpleNode n) {
        cc.gen_int_eq_reif(n);
    }

    public void int_ne(SimpleNode n) {
        cc.gen_int_ne(n);
    }

    public void int_ne_reif(SimpleNode n) {
        cc.gen_int_ne_reif(n);
    }

    public void int_le(SimpleNode n) {
        cc.gen_int_le(n);
    }

    public void int_le_reif(SimpleNode n) {
        cc.gen_int_le_reif(n);
    }

    public void int_lt(SimpleNode n) {
        cc.gen_int_lt(n);
    }

    public void int_lt_reif(SimpleNode n) {
        cc.gen_int_lt_reif(n);
    }

    // Linear bool and int constraints
    public void bool_lin_eq(SimpleNode n) {
        lc.gen_bool_lin_eq(n);
    }

    public void bool_lin_eq_reif(SimpleNode n) {
        lc.gen_int_lin_eq_reif(n);
    }

    public void bool_lin_ne(SimpleNode n) {
        lc.gen_int_lin_ne(n);
    }

    public void bool_lin_ne_reif(SimpleNode n) {
        lc.gen_int_lin_ne_reif(n);
    }

    public void bool_lin_lt(SimpleNode n) {
        lc.gen_int_lin_lt(n);
    }

    public void bool_lin_lt_reif(SimpleNode n) {
        lc.gen_int_lin_lt_reif(n);
    }

    public void bool_lin_le(SimpleNode n) {
        lc.gen_int_lin_le(n);
    }

    public void bool_lin_le_reif(SimpleNode n) {
        lc.gen_int_lin_le_reif(n);
    }

    public void int_lin_eq(SimpleNode n) {
        lc.gen_int_lin_eq(n);
    }

    public void int_lin_eq_reif(SimpleNode n) {
        lc.gen_int_lin_eq_reif(n);
    }

    public void int_lin_ne(SimpleNode n) {
        lc.gen_int_lin_ne(n);
    }

    public void int_lin_ne_reif(SimpleNode n) {
        lc.gen_int_lin_ne_reif(n);
    }

    public void int_lin_lt(SimpleNode n) {
        lc.gen_int_lin_lt(n);
    }

    public void int_lin_lt_reif(SimpleNode n) {
        lc.gen_int_lin_lt_reif(n);
    }

    public void int_lin_le(SimpleNode n) {
        lc.gen_int_lin_le(n);
    }

    public void int_lin_le_reif(SimpleNode n) {
        lc.gen_int_lin_le_reif(n);
    }

    // Diverse int operations
    public void int_min(SimpleNode n) {
        oc.gen_int_min(n);
    }

    public void int_max(SimpleNode n) {
        oc.gen_int_max(n);
    }

    public void int_mod(SimpleNode n) {
        oc.gen_int_mod(n);
    }

    public void int_div(SimpleNode n) {
        oc.gen_int_div(n);
    }

    public void int_abs(SimpleNode n) {
        oc.gen_int_abs(n);
    }

    public void int_times(SimpleNode n) {
        oc.gen_int_times(n);
    }

    public void int_plus(SimpleNode n) {
        oc.gen_int_plus(n);
    }

    public void int_pow(SimpleNode n) {
        oc.gen_int_pow(n);
    }

    public void int2float(SimpleNode n) {
        oc.gen_int2float(n);
    }

    // Element int, boolean, set and float constraints
    public void array_bool_element(SimpleNode n) {
        ec.gen_array_int_element(n);
    }

    public void array_var_bool_element(SimpleNode n) {
        ec.gen_array_var_int_element(n);
    }

    public void array_int_element(SimpleNode n) {
        ec.gen_array_int_element(n);
    }

    public void array_var_int_element(SimpleNode n) {
        ec.gen_array_var_int_element(n);
    }

    public void array_set_element(SimpleNode n) {
        ec.gen_array_set_element(n);
    }

    public void array_var_set_element(SimpleNode n) {
        ec.gen_array_var_set_element(n);
    }

    public void array_float_element(SimpleNode n) {
        ec.gen_array_float_element(n);
    }

    public void array_var_float_element(SimpleNode n) {
        ec.gen_array_var_float_element(n);
    }

    // Global constraints
    public void jacop_cumulative(SimpleNode n) {
        gc.gen_jacop_cumulative(n);
    }

    public void jacop_circuit(SimpleNode n) {
        gc.gen_jacop_circuit(n);
    }

    public void jacop_subcircuit(SimpleNode n) {
        gc.gen_jacop_subcircuit(n);
    }

    public void jacop_alldiff(SimpleNode n) {
        gc.gen_jacop_alldiff(n);
    }

    public void jacop_softalldiff(SimpleNode n) {
        gc.gen_jacop_softalldiff(n);
    }

    public void jacop_softgcc(SimpleNode n) {
        gc.gen_jacop_softgcc(n);
    }

    public void jacop_alldistinct(SimpleNode n) {
        gc.gen_jacop_alldistinct(n);
    }

    public void jacop_among_var(SimpleNode n) {
        gc.gen_jacop_among_var(n);
    }

    public void jacop_among(SimpleNode n) {
        gc.gen_jacop_among(n);
    }

    public void jacop_gcc(SimpleNode n) {
        gc.gen_jacop_gcc(n);
    }

    public void jacop_global_cardinality_closed(SimpleNode n) {
        gc.gen_jacop_global_cardinality_closed(n);
    }

    public void jacop_global_cardinality_low_up_closed(SimpleNode n) {
        gc.gen_jacop_global_cardinality_low_up_closed(n);
    }

    public void jacop_diff2_strict(SimpleNode n) {
        gc.gen_jacop_diff2_strict(n);
    }

    public void jacop_diff2(SimpleNode n) {
        gc.gen_jacop_diff2(n);
    }

    public void jacop_list_diff2(SimpleNode n) {
        gc.gen_jacop_list_diff2(n);
    }

    public void jacop_count(SimpleNode n) {
        gc.gen_jacop_count(n);
    }

    public void jacop_nvalue(SimpleNode n) {
        gc.gen_jacop_nvalue(n);
    }

    public void jacop_minimum_arg_int(SimpleNode n) {
        gc.gen_jacop_minimum_arg_int(n);
    }

    public void jacop_minimum(SimpleNode n) {
        gc.gen_jacop_minimum(n);
    }

    public void jacop_maximum_arg_int(SimpleNode n) {
        gc.gen_jacop_maximum_arg_int(n);
    }

    public void jacop_maximum(SimpleNode n) {
        gc.gen_jacop_maximum(n);
    }

    public void jacop_table_int(SimpleNode n) {
        gc.gen_jacop_table_int(n);
    }

    public void jacop_table_bool(SimpleNode n) {
        gc.gen_jacop_table_int(n);
    }

    public void jacop_assignment(SimpleNode n) {
        gc.gen_jacop_assignment(n);
    }

    public void jacop_regular(SimpleNode n) {
        gc.gen_jacop_regular(n);
    }

    public void jacop_knapsack(SimpleNode n) {
        gc.gen_jacop_knapsack(n);
    }

    public void jacop_sequence(SimpleNode n) {
        gc.gen_jacop_sequence(n);
    }

    public void jacop_stretch(SimpleNode n) {
        gc.gen_jacop_stretch(n);
    }

    public void jacop_disjoint(SimpleNode n) {
        gc.gen_jacop_disjoint(n);
    }

    public void jacop_networkflow(SimpleNode n) {
        gc.gen_jacop_networkflow(n);
    }

    public void jacop_lex_less_int(SimpleNode n) {
        gc.gen_jacop_lex_less_int(n);
    }

    public void jacop_lex_less_bool(SimpleNode n) {
        gc.gen_jacop_lex_less_int(n);
    }

    public void jacop_lex_lesseq_int(SimpleNode n) {
        gc.gen_jacop_lex_lesseq_int(n);
    }

    public void jacop_lex_lesseq_bool(SimpleNode n) {
        gc.gen_jacop_lex_lesseq_int(n);
    }

    public void jacop_value_precede_int(SimpleNode n) {
        gc.gen_jacop_value_precede_int(n);
    }

    public void jacop_bin_packing(SimpleNode n) {
        gc.gen_jacop_bin_packing(n);
    }

    public void jacop_float_maximum(SimpleNode n) {
        gc.gen_jacop_float_maximum(n);
    }

    public void jacop_float_minimum(SimpleNode n) {
        gc.gen_jacop_float_minimum(n);
    }

    public void jacop_geost(SimpleNode n) {
        gc.gen_jacop_geost(n);
    }

    public void jacop_geost_bb(SimpleNode n) {
        gc.gen_jacop_geost_bb(n);
    }


    // Set constrints
    public void set_card(SimpleNode n) {
        sc.gen_set_card(n);
    }

    public void set_diff(SimpleNode n) {
        sc.gen_set_diff(n);
    }

    public void set_eq(SimpleNode n) {
        sc.gen_set_eq(n);
    }

    public void set_eq_reif(SimpleNode n) {
        sc.gen_set_eq_reif(n);
    }

    public void set_in(SimpleNode n) {
        sc.gen_set_in(n);
    }

    public void set_in_reif(SimpleNode n) {
        sc.gen_set_in_reif(n);
    }

    public void set_intersect(SimpleNode n) {
        sc.gen_set_intersect(n);
    }

    public void set_le(SimpleNode n) {
        sc.gen_set_le(n);
    }

    public void set_le_reif(SimpleNode n) {
        sc.gen_set_le_reif(n);
    }

    public void set_lt(SimpleNode n) {
        sc.gen_set_lt(n);
    }

    public void set_lt_reif(SimpleNode n) {
        sc.gen_set_lt_reif(n);
    }

    public void set_ne(SimpleNode n) {
        sc.gen_set_ne(n);
    }

    public void set_ne_reif(SimpleNode n) {
        sc.gen_set_ne_reif(n);
    }

    public void set_subset(SimpleNode n) {
        sc.gen_set_subset(n);
    }

    public void set_subset_reif(SimpleNode n) {
        sc.gen_set_subset_reif(n);
    }

    public void set_symdiff(SimpleNode n) {
        sc.gen_set_symdiff(n);
    }

    public void set_union(SimpleNode n) {
        sc.gen_set_union(n);
    }

    // Floating-point comparisons
    public void float_eq(SimpleNode n) {
        fcc.gen_float_eq(n);
    }

    public void float_eq_reif(SimpleNode n) {
        fcc.gen_float_eq_reif(n);
    }

    public void float_ne(SimpleNode n) {
        fcc.gen_float_ne(n);
    }

    public void float_ne_reif(SimpleNode n) {
        fcc.gen_float_ne_reif(n);
    }

    public void float_le(SimpleNode n) {
        fcc.gen_float_le(n);
    }

    public void float_le_reif(SimpleNode n) {
        fcc.gen_float_le_reif(n);
    }

    public void float_lt(SimpleNode n) {
        fcc.gen_float_lt(n);
    }

    public void float_lt_reif(SimpleNode n) {
        fcc.gen_float_lt_reif(n);
    }

    // Floating-point linear constraint
    public void float_lin_eq(SimpleNode n) {
        flc.gen_float_lin_eq(n);
    }

    public void float_lin_eq_reif(SimpleNode n) {
        flc.gen_float_lin_eq_reif(n);
    }

    public void float_lin_le(SimpleNode n) {
        flc.gen_float_lin_le(n);
    }

    public void float_lin_le_reif(SimpleNode n) {
        flc.gen_float_lin_le_reif(n);
    }

    public void float_lin_lt(SimpleNode n) {
        flc.gen_float_lin_lt(n);
    }

    public void float_lin_lt_reif(SimpleNode n) {
        flc.gen_float_lin_lt_reif(n);
    }

    public void float_lin_ne(SimpleNode n) {
        flc.gen_float_lin_ne(n);
    }

    public void float_lin_ne_reif(SimpleNode n) {
        flc.gen_float_lin_ne_reif(n);
    }

    // Floating-point operations
    public void float_abs(SimpleNode n) {
        foc.gen_float_abs(n);
    }

    public void float_acos(SimpleNode n) {
        foc.gen_float_acos(n);
    }

    public void float_asin(SimpleNode n) {
        foc.gen_float_asin(n);
    }

    public void float_atan(SimpleNode n) {
        foc.gen_float_atan(n);
    }

    public void float_cos(SimpleNode n) {
        foc.gen_float_cos(n);
    }

    public void float_exp(SimpleNode n) {
        foc.gen_float_exp(n);
    }

    public void float_ln(SimpleNode n) {
        foc.gen_float_ln(n);
    }

    public void float_log10(SimpleNode n) {
        foc.gen_float_log10(n);
    }

    public void float_log2(SimpleNode n) {
        foc.gen_float_log2(n);
    }

    public void float_sqrt(SimpleNode n) {
        foc.gen_float_sqrt(n);
    }

    public void float_sin(SimpleNode n) {
        foc.gen_float_sin(n);
    }

    public void float_tan(SimpleNode n) {
        foc.gen_float_tan(n);
    }

    public void float_max(SimpleNode n) {
        foc.gen_float_max(n);
    }

    public void float_min(SimpleNode n) {
        foc.gen_float_min(n);
    }

    public void float_plus(SimpleNode n) {
        foc.gen_float_plus(n);
    }

    public void float_times(SimpleNode n) {
        foc.gen_float_times(n);
    }

    public void float_div(SimpleNode n) {
        foc.gen_float_div(n);
    }

    public void float_pow(SimpleNode n) {
        foc.gen_float_pow(n);
    }

    // public void float_cosh(SimpleNode n) {foc.gen_float_cosh(n);}
    // public void float_sinh(SimpleNode n) {foc.gen_float_sinh(n);}
    // public void float_tanh(SimpleNode n) {foc.gen_float_tanh(n);}

}
