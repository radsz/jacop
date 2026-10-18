# MiniZinc globals and extensional constraints in JaCoP (checked 2026-10-18)

Baseline: JaCoP `develop-5.0` and the MiniZinc 2.10.1 standard library. The goal is a native, efficient propagator for every global constraint MiniZinc specifies, plus state-of-the-art extensional (table) constraints.

## 1. How a global reaches JaCoP

MiniZinc rewrites every global `g(...)` to `fzn_g(...)`. If the solver library (`jacop-flatzinc/src/main/minizinc/org/jacop/minizinc/`) overrides `fzn_g`, JaCoP decides what is posted. Otherwise MiniZinc uses the standard decomposition from `std/fzn_g.mzn`, and JaCoP sees only primitive constraints (linear, reified comparisons, clauses, element).

The 2.10.1 standard library has **253 `fzn_*` predicates** (not counting `_reif`/`_imp` variants). JaCoP overrides **72**:

| Status | Count | Meaning |
|---|---|---|
| Native | 66 | Override posts a `jacop_*` constraint backed by a Java propagator |
| Native via another global | 6 | `disjunctive`, `disjunctive_strict` → cumulative; `diffn_k` → geost; `diffn_nonstrict` → diff2; `distribute`, `exactly_int` → count |
| MiniZinc decomposition | 181 | Not overridden. 60 of these are the new `count_*` bool/float/set variants. |

**Update.** Since this check, `develop-5.0` also posts natively: `cumulatives`, `cumulatives_opt`, `sliding_among_int/bool` and all `count_*_bool` variants (including `_par` and `_reif`). `bin_packing*_opt` and reified `regular` turned out to reach native propagators already through MiniZinc's default bodies. The counts below are from the original check.

Reified forms: the standard library has 188 `fzn_*_reif` files. JaCoP overrides only 13 (`all_equal_int`, `among`, `at_least/at_most`, `count_*`, `member_*`, `nvalue`). Every other reified global, including `table`, `all_different` and `global_cardinality`, is decomposed.

## 2. Natively supported today

all_different_int, alldifferent_except, alldifferent_except_0, all_equal_int, among, arg_max/arg_min (int, bool), at_least/at_most (int), bin_packing (plain, capa, load, and their opt forms), circuit, subcircuit, count_eq (+par), count_geq/gt/leq/lt (par), count_* over bool (all forms), cumulative, cumulative_opt, cumulatives, cumulatives_opt, diffn, diffn_k, diffn_nonstrict, disjoint, disjunctive, disjunctive_strict, disjunctive_opt, disjunctive_strict_opt, distribute, exactly_int, geost, geost_bb, global_cardinality (all four int variants), if_then_else (bool/int/float/set, par and var), increasing (int, bool), strictly_increasing_int, int_set_channel, inverse, knapsack, lex_less/lex_lesseq (int, bool), link_set_to_booleans, member (int, bool), network_flow, network_flow_cost, nvalue, partition_set, regular (also reified), regular_set, seq_precede_chain_int, sliding_among (int, bool), table_int, table_bool, value_precede_int, value_precede_chain_int.

## 3. Gaps, ordered by impact

### 3a. JaCoP already has a propagator, only the MiniZinc wiring is missing (cheap)
| MiniZinc global | Existing JaCoP class | Notes |
|---|---|---|
| `mdd`, `mdd_nondet` | `ExtensionalSupportMdd` | Needs translation from MiniZinc's MDD encoding to JaCoP's `MDD` |
| `sliding_sum` | `SumWeight`/`LinearInt` | Needs its own propagator or a chain of `LinearInt` (`sliding_among` is done, via `Sequence`) |
| `lex_chain_less(eq)_int/bool`, `lex2`, `strict_lex2` | `LexOrder` (pairwise) | Pairwise chaining is weaker than a dedicated lex-chain propagator, but better than MiniZinc's decomposition |
| `all_different_int_opt`, `alldifferent_except` with an `except` set (2.10) | `Alldistinct`, `AlldifferentExcept` | The opt version maps to an except-value encoding |
| `circuit_opt`, `inverse_opt` | `Subcircuit` | The optional forms can be expressed with JaCoP's optional-task machinery |
| `count_neq`, `count_*` (var count), `at_least/at_most/exactly_set` | `Count*`, `AtLeast`/`AtMost` | Small library additions |
| `increasing_float`, `strictly_increasing_float`, `lex_*_float` | `jacop-floats` | Float versions of existing int propagators |
| `member_set`, `set_member`, `all_different_set`, `all_disjoint`, `all_equal_set`, `increasing_set`, `lex_*_set`, `value_precede*_set`, `global_cardinality_set` | `jacop-sets` | Set versions; lower priority for the MiniZinc Challenge |
| `table_int_reif` | `Table` | Needs a reified version, see section 4 (reified `regular` already reaches `Regular`) |

### 3b. New propagators needed (medium/large)
- **Scheduling with optional tasks:** `alternative`, `span`, `disjunctive_strict_opt` beyond the current form, `cumulative` with variable resource. These appear often in MiniZinc Challenge scheduling models.
- **Sorting family:** `sort`, `arg_sort_int/float`, `arg_val_*`. JaCoP has no sortedness propagator.
- **Graph family:** `connected`, `dconnected`, `tree`, `dtree`, `path`, `dpath`, `bounded_path`, `reachable`, `dreachable`, `steiner`, `dsteiner`, `wst`, `dwst`, `dag`, `subgraph`. JaCoP has graph matching constraints in `jacop.mzn` but none of the MiniZinc graph globals.
- **Cost automata:** `cost_regular`, `cost_mdd`, `regular_nfa`, `regular_regexp` (the last is a front-end translation to `regular`).
- **Others:** `symmetric_all_different`, `inverse_set`, `inverse_in_range`, `roots`, `range`, `piecewise_linear` (+ non-continuous), `var_perm_sym`, `var_sqr_sym`, `neural_net`, `arg_max/min_float`, `write`/`writes`/`writes_seq`, `sum_pred`, `sum_set`, `geost_nonoverlap_k`, `geost_smallest_bb`, `diffn_nonstrict_k`, `seq_precede_chain_set`, `fzn_assume` (2.10), `blackbox` (2.10).

### 3c. Library hygiene that blocks "following the standard"
- Rename mznlib parameters to the canonical std names (`xs`, `start`, `duration`, …). MiniZinc 2.10 resolves reified versions by parameter name, so mismatches will break once native predicates accept named arguments. Today they only produce warnings under `--warn-non-authoritative-names`.
- Provide native `_reif`/`_imp` versions where JaCoP's `Reified` wrapper or a dedicated propagator can do it. Without them every reified global falls back to a decomposition.
- Remove legacy non-`fzn_` overrides (`all_distinct.mzn`, `GCC.mzn`, `diff2.mzn`, `among_var.mzn`, `channel.mzn`) unless they are still referenced.

## 4. Extensional constraints

### What JaCoP has
| Class | Algorithm | Used from MiniZinc? |
|---|---|---|
| `table/Table` | Compact-Table (Demeulenaere et al., CP 2016) on a reversible sparse bit-set | Yes, `table_int` with more than 64 tuples |
| `table/SimpleTable` | Compact-Table restricted to at most 64 tuples (single word) | Yes, at most 64 tuples (tiny tables become direct conflict constraints) |
| `ExtensionalSupportStr` | STR / STR2-style simple tabular reduction | No |
| `ExtensionalSupportVa`, `ExtensionalConflictVa` | Valid/allowed-tuple search (GAC-va) | No |
| `ExtensionalSupportMdd` | MDD-based GAC | No |
| `regular/Regular` | Layered-graph (Pesant) GAC for `regular` | Yes |

So the core algorithm is the right one: Compact-Table is still the reference GAC propagator for positive tables. The implementation, however, is behind current best practice.

### Gaps in the Compact-Table implementation (`jacop-core/.../constraints/table/Table.java`, `AbstractTable.java`)
1. **Boxed, hash-based supports.** `supports` and `residues` are `HashMap<Integer, long[]>`/`HashMap<Integer, Integer>` per variable, and `varMap` is a map lookup per update. CT implementations index a dense `long[][]` by `value - offset` and keep int residues in an array. Every value test currently boxes an `Integer` and hashes it.
2. **Allocation in the hot path.** `computeDelta` returns `new Object[] {delta, rp}` and builds `rp = previousDomain.subtract(currentDomain)` as a new `IntDomain` each time a variable changes. `ReversibleSparseBitSet.intersectWithMask` allocates a new `long[words]` on every call.
3. **Delta relative to the previous search level, not the last propagation.** CT keeps `lastSize[x]` per variable and computes the delta since this constraint last ran. JaCoP uses `getPreviousDomain()`, which re-processes removals from earlier propagations at the same level. This is correct (the mask is idempotent) but does redundant work, and the reset-based update triggers less often than it should.
4. **No word-level support offsets.** CT stores, for each `(x, a)`, only the words between the first and last non-zero word. JaCoP allocates a full-length `long[]` per value, which costs memory and time on large tables.
5. **Filtering re-checks the variable that caused the update.** CT skips the filtering step for a variable when it was the only one whose domain changed since the last run. JaCoP filters every non-singleton variable on every run.

**Front-end bug (memory blow-up), fixed.** `GlobalConstraints.deduplicateTableRows` (`jacop-flatzinc/.../fz/constraints/GlobalConstraints.java:1098`) allocates each row as `new ArrayList<>(t.length)`, so the capacity is the number of tuples instead of the arity. Memory is quadratic in the table size. MiniZinc's `regression/bug284` (2 variables, 250,164 tuples) runs out of memory with a 12 GB heap for this reason, and Gecode solves it instantly. Fixed by allocating `new ArrayList<>(t[i].length)`; the instance now solves in about a second. Sorting `int[]` rows directly without boxing would be faster still.

### Missing extensional features (state of the art)
| Feature | Reference | Why it matters |
|---|---|---|
| Short tables (`*` wildcards), **CT\*** | Verhaeghe, Lecoutre, Schaus, CP 2017 | Compresses tables massively; XCSP3 and many generators produce them |
| Basic smart tables, **CT^bs** | Verhaeghe et al., CP 2017/2018 | Tuples with unary/binary conditions (`x < y`, `x ≠ v`) |
| Negative tables, **CT-neg** | Verhaeghe et al., CP 2017 | Efficient GAC for conflict tables; JaCoP only has the older `ExtensionalConflictVa` |
| Reified / half-reified table | Common in MiniZinc models | MiniZinc decomposes `table_int_reif` into huge clause sets when the solver has no native version |
| Table on optional variables (`table_int_opt`) | MiniZinc 2.7+ | Currently decomposed |
| MDD propagator, **MDD4R** and compressed MDD | Perez & Régin, CP 2014; Verhaeghe et al. | `mdd`/`mdd_nondet`/`cost_mdd` are MiniZinc globals; JaCoP's `ExtensionalSupportMdd` is the older algorithm and is not wired |
| Explanations for table (for LCG later) | Chuffed, OR-Tools CP-SAT | Needed once lazy clause generation starts, kept as the last step |
| Front-end table preprocessing | Most CP solvers | Merge tables on the same scope, detect `table` that is an `element` or `regular`, compress to short tables before posting |

## 5. Suggested order of work

1. **Test bench first.** One JUnit suite per global that, for small random instances, compares (a) the native propagator, (b) the MiniZinc decomposition and (c) brute-force enumeration: same solution set, and native pruning at least as strong as the decomposition. Run it on every change. This doubles as the correctness bench Radek asked for.
2. **Compact-Table rewrite** (gaps 1–5 above) behind the same `Table` API, benchmarked against the current implementation on the `jacop-benchmarks` FlatZinc instances that use `table_int`.
3. **CT\*, CT-neg and reified table**, then wire `table_int_reif`, `table_int_opt` and conflict tables from the front end.
4. **Wire the "propagator exists" globals** from section 3a, starting with `mdd`, `sliding_sum`, `lex_chain`, `all_different` with an `except` set, and `count_*` var.
5. **New propagators** from section 3b, starting with the scheduling family (`alternative`, `span`) and `sort`/`arg_sort`, then the graph family.
6. **Library hygiene** from section 3c alongside the above, so each new override uses the canonical parameter names.
