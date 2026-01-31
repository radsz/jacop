# MethodName checkstyle violations – categorized

**Rule pattern:** `^(?![a-z]$)(?![a-z][A-Z])[a-z][a-z0-9]*(?:[A-Z][a-z0-9]*)*(?:_[0-9]+)*$`

Allowed: camelCase (must not be single letter, must not be `xVar`-style), with optional trailing `_[0-9]+` only.

**Total unique violating method names:** 444 (508 violation occurrences).

---

## Category 1: Snake_case (underscore between words)

**Cause:** Pattern allows only trailing `_[0-9]+`. Any underscore between words (e.g. `word_word`) violates.

**Count:** Vast majority (~430+ unique names).

**Examples:**
- `no_sum`, `consistencyWhen_LB0_EQ_UB0`, `circle_intersection`, `six_hump_camel_function`, `tiny_tsp`, `curve_fitting3`, `markov_chains_taha`, `min_cost_flow`, `problem_kaye_splitter`
- All `gen_*` (e.g. `gen_bool_and`, `gen_int_eq`, `gen_bool2int`, `gen_jacop_alldiff`, …)
- All `int_*` (e.g. `int_eq`, `int_lin_eq`, `int_comparison`, …)
- All `bool_*`, `float_*`, `set_*`, `array_*`, `jacop_*`
- `clause_generation`, `count_eq_imp`, `generate_clause`, `generate_eq`, etc.

**Full list (unique, alphabetical):**  
array_bool_and, array_bool_and_imp, array_bool_element, array_bool_or, array_bool_or_imp, array_bool_xor, array_bool_xor_imp, array_float_element, array_int_element, array_set_element, array_var_bool_element, array_var_float_element, array_var_int_element, array_var_set_element, bool_and, bool_and_imp, bool_clause, bool_clause_imp, bool_clause_reif, bool_eq, bool_eq_imp, bool_eq_reif, bool_ge_imp, bool_gt_imp, bool_le, bool_le_imp, bool_le_reif, bool_lin_eq, bool_lin_eq_reif, bool_lin_le, bool_lin_le_reif, bool_lin_lt, bool_lin_lt_reif, bool_lin_ne, bool_lin_ne_reif, bool_lt, bool_lt_imp, bool_lt_reif, bool_ne, bool_ne_imp, bool_ne_reif, bool_not, bool_or, bool_xor, bool_xor_imp, circle_intersection, clause_generation, count_eq_imp, float_abs, float_acos, float_asin, float_atan, float_ceil, float_comparison, float_cos, float_div, float_eq, float_eq_reif, float_exp, float_floor, float_le, float_le_reif, float_lin_eq, float_lin_eq_reif, float_lin_le, float_lin_le_reif, float_lin_lt, float_lin_lt_reif, float_lin_ne, float_lin_ne_reif, float_lin_relation, float_ln, float_log10, float_log2, float_lt, float_lt_reif, float_max, float_min, float_ne, float_ne_reif, float_plus, float_pow, float_round, float_sin, float_sqrt, float_tan, float_times, gen_array_bool_and, gen_array_bool_and_imp, gen_array_bool_element, gen_array_bool_or, gen_array_bool_or_imp, gen_array_bool_xor, gen_array_bool_xor_imp, gen_array_float_element, gen_array_int_element, gen_array_set_element, gen_array_var_float_element, gen_array_var_int_element, gen_array_var_set_element, gen_bool_and, gen_bool_and_imp, gen_bool_clause, gen_bool_clause_imp, gen_bool_clause_reif, gen_bool_eq, gen_bool_eq_imp, gen_bool_eq_reif, gen_bool_ge_imp, gen_bool_gt_imp, gen_bool_le, gen_bool_le_imp, gen_bool_le_reif, gen_bool_lin_eq, gen_bool_lt, gen_bool_lt_imp, gen_bool_lt_reif, gen_bool_ne, gen_bool_ne_imp, gen_bool_ne_reif, gen_bool_not, gen_bool_or, gen_bool_xor, gen_bool_xor_imp, gen_bool2int, gen_count_eq_imp, gen_float_*, gen_int_*, gen_jacop_*, gen_link_set_to_booleans, gen_partition_set, gen_set_*, int_*, jacop_*, no_sum, problem_kaye_splitter, set_*, six_hump_camel_function, tiny_tsp, (and all other names containing underscore between words).

---

## Category 2: Underscore + capitals / mixed (e.g. S_Est, LB0_EQ_UB0)

**Cause:** Underscore in the middle with capital letters or non-digit segment after underscore.

**Exact names:**
- `consistencyWhen_LB0_EQ_UB0` (AmongVar.java)
- `removeFromS_Est` (Cumulative.java)
- `removeFromS_Lct` (Cumulative.java)

---

## Category 3: Leading capital (PascalCase)

**Cause:** First character must be `[a-z]`; names starting with uppercase violate.

**Exact names:**
- `FindGeneralizedMatching` (GCC.java)
- `ReachedFromY` (GCC.java)
- `SCCs` (GCC.java)
- `SCCsWithoutS` (GCC.java)

---

## Category 4: Second character uppercase (xVar-style)

**Cause:** Pattern disallows `[a-z][A-Z]` (lowercase immediately followed by uppercase).

**Exact names:**
- `nVarIn` (Pruning.java)
- `nVarInShift` (Pruning.java)
- `sVarInDom` (Pruning.java)
- `wVarIn` (Pruning.java)
- `xVarInMax` (Pruning.java)
- `xVarInMin` (Pruning.java)

---

## Category 5: Single lowercase letter

**Cause:** Single-letter names are disallowed by `(?![a-z]$)`.

**Exact names:**
- `e` (Task.java – cumulative)

---

## Summary by category

| Category | Cause | Example names | Approx. count (unique) |
|----------|--------|----------------|--------------------------|
| 1. Snake_case | Underscore between words | no_sum, gen_bool_and, int_eq, jacop_alldiff | ~430 |
| 2. Underscore + mixed | _LB0, S_Est, S_Lct | consistencyWhen_LB0_EQ_UB0, removeFromS_Est, removeFromS_Lct | 3 |
| 3. Leading capital | PascalCase | FindGeneralizedMatching, SCCs, SCCsWithoutS, ReachedFromY | 4 |
| 4. Second char uppercase | xVar-style | xVarInMax, xVarInMin, nVarIn, nVarInShift, wVarIn, sVarInDom | 6 |
| 5. Single letter | Single [a-z] | e | 1 |

**Total:** 444 unique method names, 508 violation occurrences.

---

## Where they appear

- **jacop-core:** AmongVar, Binpacking, Cumulative, GCC, netflow/Pruning; plus many in flatzinc-related generation (gen_*, int_*, bool_*, jacop_*, etc.).
- **jacop-flatzinc:** Bulk of `gen_*`, `int_*`, `bool_*`, `float_*`, `set_*`, `jacop_*` (constraint/FlatZinc mapping).
- **jacop-floats:** Examples (circle_intersection, six_hump_camel_function, etc.) and float_*.
- **jacop-sat:** generate_* (SatTranslation).
- **jacop-sets:** set_*.

To fix without “silencing” the rule: rename to camelCase (and keep optional trailing `_[0-9]+` only). For example: `no_sum` → `noSum`, `consistencyWhen_LB0_EQ_UB0` → `consistencyWhenLb0EqUb0`, `removeFromS_Est` → `removeFromSEst`, `FindGeneralizedMatching` → `findGeneralizedMatching`, `xVarInMax` → `xVarInMax` is already camel but violates due to second character; use e.g. `xvarInMax` or `flowVarInMax`, `e` → e.g. `end` or `endTime` (depending on meaning).
