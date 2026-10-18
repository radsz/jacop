# JaCoP development priorities

Goal: make JaCoP a state-of-the-art constraint programming solver. These priorities were set in October 2026 and decide what gets worked on, in order.

## In scope

1. **Fix open correctness bugs first, backed by a good test bench.**
   This is the most immediate priority. Every fix comes with tests that would have caught the bug, and the test bench has to be trustworthy enough to rely on for everything that follows. Known items include #71 (`network_flow_cost` missing solutions), #78 (NPE in `NoGood`), #47 and #64 (asserts used instead of `FailException`), and the failures listed in `doc/minizinc/jacop-minizinc-support.md`.

2. **Support the latest MiniZinc release.**
   Follow the MiniZinc standard: the FlatZinc format, the solver configuration (`org.jacop.msc`), the standard library's `fzn_*` hooks and redefinitions, and its parameter naming. See `doc/minizinc/jacop-minizinc-support.md`.

3. **A native, efficient implementation of every global constraint MiniZinc specifies.**
   Each `fzn_*` global in the MiniZinc standard library should map to a JaCoP propagator rather than to MiniZinc's decomposition, including reified versions where they matter. See `doc/minizinc/globals-and-extensional.md` for the current coverage and gaps.

4. **State-of-the-art extensional constraints.**
   Bring the table constraints up to current practice: an efficient Compact-Table, short tables (CT\*), negative tables, smart tables, reified and optional-variable tables, and modern MDD propagation. See `doc/minizinc/globals-and-extensional.md`, section 4.

5. **Lazy clause generation (long term, last).**
   Explanations for propagators and LCG are wanted, but not soon. They come after the items above.

## Out of scope for now

- Smarter LNS and solution-guided search.
- Parallel search.
