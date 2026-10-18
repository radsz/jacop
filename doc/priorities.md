# JaCoP development priorities

Goal: make JaCoP a state-of-the-art constraint programming solver. These priorities were set in October 2026 and decide what gets worked on, in order.

## In scope

1. **Fix open correctness bugs first, backed by a good test bench.**
   This is the most immediate priority. Every fix comes with tests that would have caught the bug, and the test bench has to be trustworthy enough to rely on for everything that follows. Known items include #71 (`network_flow_cost` missing solutions), #78 (NPE in `NoGood`), #47 and #64 (asserts used instead of `FailException`), and the failures listed in `doc/minizinc/jacop-minizinc-support.md`.
   *Status:* #30, #46, #47, #64, #71 and #78 are fixed in `develop-5.0` (PR #81), as are the table memory blow-up, the FlatZinc front end dropping reifications, `bin_packing_capa` bin numbering, `jacop_sequence` with gapped value sets, and three `Cumulative`/`CumulativeOptional` bugs. PR #87 then fixed another batch found by brute-force testing: `Regular` (also affects `Sequence`), `LinearIntDom`, strict `Lex`, `ExtensionalConflictVa`, `Mdd`, `CumulativeBasic`, `ElementVariable`, `Knapsack`, `XltY`/`XgtY`/`XneqY`, several `IntervalDomain`/`SmallDenseDomain` operations, the FlatZinc posting of `among`, `circuit`, `table`, `global_cardinality` and `cumulative`, and the mznlib versions of closed `global_cardinality`, `knapsack`, `bin_packing`, `network_flow` and `value_precede_chain`. Still open from the MiniZinc suite: the nested `seq_search` NPE and the `tuple_if_then_else` stack overflow.
   *Test bench:* CI runs on GitHub Actions (`-Pcommit verify`, PR #80); JaCoP's internal consistency checks now run in every test (PR #85); `GlobalConstraintBruteForceTest` compares all solutions of 61 global constraints on small random domains with brute-force enumeration, `DomainOperationsBruteForceTest` does the same for domain operations, `MznlibGlobalsTest` compares JaCoP's mznlib against MiniZinc's decompositions, and `scripts/minizinc-differential.py` compares JaCoP with Chuffed on random one-global MiniZinc models (PR #87). Not yet covered: whole FlatZinc models whose expected results are confirmed by other solvers.

2. **Support the latest MiniZinc release.**
   Follow the MiniZinc standard: the FlatZinc format, the solver configuration (`org.jacop.msc`), the standard library's `fzn_*` hooks and redefinitions, and its parameter naming. See `doc/minizinc/jacop-minizinc-support.md`.
   *Status:* `org.jacop.msc` is generated at build time and works with MiniZinc 2.10.1 (#74, #75, #79), and `set_superset(_reif)` and `bool_or_imp` are implemented. Still open: `on_restart` meta-search and canonical mznlib parameter names.

3. **A native, efficient implementation of every global constraint MiniZinc specifies.**
   Each `fzn_*` global in the MiniZinc standard library should map to a JaCoP propagator rather than to MiniZinc's decomposition, including reified versions where they matter. See `doc/minizinc/globals-and-extensional.md` for the current coverage and gaps.
   *Status:* the hooks MiniZinc added in 2.8 to 2.10 are covered except the experimental `assume` and `blackbox` (`cumulatives(_opt)`, `sliding_among` and `count_*_bool` are native, `bin_packing*_opt` and reified `regular` reach native propagators). Next: the cheap wiring in section 3a, then new propagators.

4. **State-of-the-art extensional constraints.**
   Bring the table constraints up to current practice: an efficient Compact-Table, short tables (CT\*), negative tables, smart tables, reified and optional-variable tables, and modern MDD propagation. See `doc/minizinc/globals-and-extensional.md`, section 4.
   *Status:* not started. Only correctness fixes have landed (table memory blow-up in PR #82; empty tables, `Mdd` and `ExtensionalConflictVa` in PR #87); the Compact-Table performance gaps are all still open.

5. **Lazy clause generation (long term, last).**
   Explanations for propagators and LCG are wanted, but not soon. They come after the items above.
   *Status:* not started.

## Open candidates for the next task (October 2026)

- Priority 1: the nested `seq_search` NPE and the `tuple_if_then_else` stack overflow; whole-model FlatZinc tests with results confirmed by other solvers; a check that native pruning is at least as strong as the decomposition.
- Priority 2: `on_restart` meta-search; canonical mznlib parameter names.
- Priority 3: the cheap wiring in `globals-and-extensional.md` section 3a (`mdd`, `sliding_sum`, `lex_chain`, `all_different` with an `except` set, `count_*` with a variable count, `table_int_reif`), then new propagators (section 3b), and the experimental `blackbox` and `assume` hooks.
- Priority 4: the Compact-Table rewrite, then CT\*, CT-neg and reified tables.

## Out of scope for now

- Smarter LNS and solution-guided search.
- Parallel search.
