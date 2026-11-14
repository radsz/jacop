#!/usr/bin/env python3
"""Adds MiniZinc models to the FlatZinc regression suite with golden outputs cross-checked by
Gecode and Chuffed, and re-verifies tests added this way.

A test directory <category>/<name>/ holds:
  <name>.mzn       the model, its search annotation made deterministic when needed
  <name>.fzn       the model flattened with the JaCoP MiniZinc library
  <name>.out       JaCoP's output, the golden result the test runner compares against
  options.opt      only for models whose solutions are all enumerated (-n 1000000)
  metadata.json    the FlatZinc builtins and constraint families the .fzn uses
  crosscheck.txt   what was verified, and with which solvers

Two modes:
  all    satisfaction models with few solutions: JaCoP enumerates every solution, and the set of
         solutions must equal the sets found by Gecode and Chuffed.
  fixed  larger satisfaction models and optimisation models: the search annotation of the solve
         item is rewritten to input_order/indomain_min and followed by an input_order/
         indomain_min search on all other top-level decision variables, so depth-first search
         reaches the lexicographically smallest solution (or, when optimising, the
         lexicographically smallest optimal solution) whatever the propagation strength. The first
         solution (satisfaction) or the last one (optimisation) must be identical for all three
         solvers, and every solver must prove optimality.
Solutions are compared as printed with --output-mode dzn, that is the values of all the model's
variables. In both modes each golden JaCoP solution (up to 20 of them) is also fed back to Gecode
as data fixing those variables, and Gecode must accept it as a solution of the original model.

Requirements: MiniZinc on the PATH (or in MINIZINC) with Gecode and Chuffed (both come with the
MiniZinc bundle) and the JaCoP solver configuration (org.jacop) installed; JACOP_CLASSPATH must
name the JaCoP jar(s), e.g. jacop-all/target/jacop-all-<version>.jar plus slf4j-api.

usage: scripts/minizinc-crosscheck.py add <model.mzn> [--mode auto|all|fixed] [--name NAME]
                                          [--category upTo5sec] [--source FILE --note TEXT]
                                          [--origin TEXT]
                                          [--gecode-differs REASON]
       scripts/minizinc-crosscheck.py verify <test dir>...
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

MZN = os.environ.get("MINIZINC", "minizinc")
JACOP = ["java", "-Xss100M", "-cp", os.environ.get("JACOP_CLASSPATH", ""), "org.jacop.fz.Fz2jacop"]
FZ_ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "jacop-benchmarks", "src",
                       "test", "fz")
ALL_SOLUTIONS = ["-n", "1000000"]
MAX_ALL = 1000          # at most this many solutions for mode all
MAX_JACOP_SECONDS = 3.0  # golden run must be fast: the suite runs every test on each commit
SOLVER_TIMEOUT = 120
FEASIBILITY_CHECKS = 20
SOL = "----------"
DONE = "=========="

VAR_HEURISTICS = ("input_order", "first_fail", "anti_first_fail", "smallest", "largest",
                  "occurrence", "most_constrained", "max_regret", "dom_w_deg", "impact")
VAL_HEURISTICS = ("indomain_min", "indomain_max", "indomain_middle", "indomain_median",
                  "indomain_random", "indomain_split", "indomain_reverse_split",
                  "indomain_interval", "indomain", "outdomain_min", "outdomain_max")


class CheckError(Exception):
    pass


def run(cmd, timeout=SOLVER_TIMEOUT, stdin=None):
    env = dict(os.environ)
    env.pop("JAVA_TOOL_OPTIONS", None)
    start = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, input=stdin,
                           env=env)
    except subprocess.TimeoutExpired:
        raise CheckError(f"timeout after {timeout}s: {' '.join(cmd)}")
    return p, time.time() - start


def strip_comments(text):
    return re.sub(r"%[^\n]*", lambda m: " " * len(m.group(0)), text)


def solve_item(text):
    """(start, end) of the solve item, ignoring commented-out ones"""
    m = re.search(r"(?m)^\s*solve\b[^;]*;", strip_comments(text))
    if not m:
        raise CheckError("no solve item")
    return m.start(), m.end()


def is_optimisation(text):
    s, e = solve_item(text)
    return re.search(r"\b(minimize|maximize)\b", text[s:e]) is not None


DECLARATION = re.compile(r"(?m)^\s*(array\s*\[[^\]]*\]\s*of\s+)?var\s+([^:;=]+?)\s*:\s*(\w+)"
                         r"\s*(::[^;=]*)?;")


def decision_variables(text):
    """top-level variables declared without a right-hand side, by kind, in declaration order"""
    found = {"int": [], "bool": [], "set": []}
    for m in DECLARATION.finditer(strip_comments(text)):
        array, kind, name = m.group(1), m.group(2).strip(), m.group(3)
        if kind.startswith("opt") or "float" in kind or re.search(r"\d\.\d", kind):
            raise CheckError(f"mode fixed does not handle the float or optional variable {name}")
        kind = "bool" if kind == "bool" else "set" if kind.startswith("set") else "int"
        found[kind].append(f"array1d({name})" if array else f"[{name}]")
    return found


def fix_search(text):
    """make depth-first search deterministic: the solve item's search annotation gets
    input_order/indomain_min, followed by a search on every other decision variable"""
    s, e = solve_item(text)
    item = re.sub(r"%[^\n]*", "", text[s:e])
    if re.search(r"\bfloat_search\b|\brestart_|\bint_default_search\b|\bwarm_start", item):
        raise CheckError("mode fixed does not handle float_search, restarts or default search")
    item = re.sub(r"\b(%s)\b" % "|".join(VAR_HEURISTICS), "input_order", item)
    item = re.sub(r"\b(%s)\b" % "|".join(VAL_HEURISTICS), "indomain_min", item)
    m = re.match(r"(\s*solve\s*)(?:::\s*(.*?))?\s*(satisfy|minimize|maximize)\b(.*)$", item, re.S)
    if not m:
        raise CheckError("cannot parse the solve item")
    searches = [m.group(2).strip()] if m.group(2) else []
    for kind, names in decision_variables(text).items():
        if names:
            searches.append(f"{kind}_search({' ++ '.join(names)}, input_order, indomain_min, "
                            f"complete)")
    if not searches:
        raise CheckError("no decision variables to search on")
    item = f"{m.group(1)}:: seq_search([\n    " + ",\n    ".join(searches) + f"])\n  " \
           f"{m.group(3)}{m.group(4)}"
    return text[:s] + item + text[e:]


def canonical_sets(text):
    """write set values one way: solvers print {1,2,3}, 1..3 or {1, 2, 3} for the same set"""
    def expand(m):
        return "{" + ",".join(map(str, range(int(m.group(1)), int(m.group(2)) + 1))) + "}"
    text = re.sub(r"(?<![\w.])(-?\d+)\.\.(-?\d+)(?![\w.])", expand, text)
    def sort_set(m):
        items = [x.strip() for x in m.group(1).split(",") if x.strip()]
        if not all(re.fullmatch(r"-?\d+", x) for x in items):
            return m.group(0)
        return "{" + ",".join(map(str, sorted(set(int(x) for x in items)))) + "}"
    text = re.sub(r"\{([^{}]*)\}", sort_set, text)
    return re.sub(r"\{\s*\}", "{}", text)


def blocks(output):
    """solution texts and whether the search was complete"""
    lines = output.split("\n")
    sols, cur, complete = [], [], False
    for line in lines:
        if line.strip() == SOL:
            sols.append(canonical_sets("\n".join(cur).strip()))
            cur = []
        elif line.strip() == DONE:
            complete = True
        elif line.strip() in ("=====UNSATISFIABLE=====", "=====ERROR=====", "=====UNKNOWN====="):
            raise CheckError("solver reported " + line.strip())
        elif not line.startswith("%"):
            cur.append(line)
    return sols, complete


def compile_jacop(mzn, fzn, ozn):
    p, _ = run([MZN, "-c", "--solver", "org.jacop", "--output-mode", "dzn", mzn, "-o", fzn,
                 "--output-ozn-to-file", ozn])
    if p.returncode != 0:
        raise CheckError("JaCoP flattening failed:\n" + p.stderr[-2000:])
    # drop the header comment, it names local paths
    lines = open(fzn).read().split("\n")
    while lines and lines[0].startswith("%"):
        lines.pop(0)
    with open(fzn, "w") as f:
        f.write("\n".join(lines))


def solve_with(solver, mzn, all_solutions, data=None, timeout=SOLVER_TIMEOUT):
    cmd = [MZN, "--solver", solver, "--output-mode", "dzn", mzn]
    if all_solutions:
        cmd.append("-a")
    if data:
        cmd.append(data)
    p, t = run(cmd, timeout)
    if p.returncode != 0:
        raise CheckError(f"{solver} failed:\n" + (p.stderr or p.stdout)[-2000:])
    return blocks(p.stdout) + (t,)


def solver_version(solver):
    p, _ = run([MZN, "--solvers"])
    for line in p.stdout.splitlines():
        if re.search(r"\(org\.\w+\.%s\b|\b%s\b" % (solver, solver), line, re.I):
            return line.strip().split(" (")[0]
    return solver


def golden(fzn, out, all_solutions):
    """runs JaCoP the way the test runner does; the runner adds ========== itself"""
    p, t = run(JACOP + (ALL_SOLUTIONS if all_solutions else []) + ["--outputfile", out, fzn])
    if p.returncode != 0 or not os.path.exists(out):
        raise CheckError("JaCoP failed:\n" + p.stderr[-2000:])
    if any(line.strip() == DONE for line in p.stdout.splitlines()):
        with open(out, "a") as f:
            f.write(DONE + "\n")
    return t


def write_metadata(test_dir, fzn):
    families = json.load(open(os.path.join(FZ_ROOT, "constraint-families.json")))
    family_of = {b: f for f, bs in families.items() for b in bs}
    builtins = sorted(set(re.findall(r"(?m)^constraint\s+(\w+)\s*\(", open(fzn).read())))
    fams = sorted({family_of[b] for b in builtins if b in family_of})
    arr = lambda xs: "[" + ", ".join(f'"{x}"' for x in xs) + "]"
    with open(os.path.join(test_dir, "metadata.json"), "w") as f:
        f.write(f'{{\n  "fznBuiltins": {arr(builtins)},\n  "constraintFamilies": {arr(fams)},\n'
                f'  "domains": []\n}}\n')


GECODE_DIFFERS = "gecode differs: "


def verify(test_dir, gecode_differs=None):
    """cross-check the golden output of one test directory; returns the crosscheck.txt text.
    gecode_differs, or the matching line of an existing crosscheck.txt, names a known difference
    of Gecode from the MiniZinc library; Gecode is then left out and Chuffed checks feasibility"""
    name = os.path.basename(os.path.normpath(test_dir))
    report = os.path.join(test_dir, "crosscheck.txt")
    if gecode_differs is None and os.path.exists(report):
        for line in open(report):
            if line.startswith(GECODE_DIFFERS):
                gecode_differs = line[len(GECODE_DIFFERS):].strip()
    solvers = ("chuffed",) if gecode_differs else ("gecode", "chuffed")
    checker = solvers[0]
    mzn = os.path.join(test_dir, name + ".mzn")
    fzn = os.path.join(test_dir, name + ".fzn")
    out = os.path.join(test_dir, name + ".out")
    all_mode = os.path.exists(os.path.join(test_dir, "options.opt"))
    text = open(mzn).read()
    opt = is_optimisation(text)
    work = tempfile.mkdtemp(prefix="crosscheck-")
    try:
        compile_jacop(mzn, os.path.join(work, "m.fzn"), os.path.join(work, "m.ozn"))
        if open(os.path.join(work, "m.fzn")).read() != open(fzn).read():
            raise CheckError("stored .fzn differs from the one the current JaCoP library produces")
        p, _ = run([MZN, "--ozn-file", os.path.join(work, "m.ozn")], stdin=open(out).read())
        jacop, jacop_complete = blocks(p.stdout)
        if not jacop:
            raise CheckError("golden output has no solution")
        results = {"JaCoP": (jacop, jacop_complete)}
        for solver in solvers:
            sols, complete, _ = solve_with(solver, mzn, all_mode)
            results[solver] = (sols, complete)

        for solver, (sols, complete) in results.items():
            if (all_mode or opt) and not complete:
                raise CheckError(f"{solver} did not complete the search")
            if not sols:
                raise CheckError(f"{solver} found no solution")
        if all_mode:
            ref = set(jacop)
            diff = [f"{solver} finds {len(set(sols))} distinct, e.g. differing "
                    f"{sorted(ref ^ set(sols))[:2]}"
                    for solver, (sols, _) in results.items() if set(sols) != ref]
            if diff:
                raise CheckError(f"solution sets differ: JaCoP finds {len(ref)} distinct; "
                                 + "; ".join(diff))
            summary = f"{len(ref)} distinct solutions"
        else:
            pick = (lambda s: s[-1]) if opt else (lambda s: s[0])
            ref = pick(jacop)
            diff = [f"{solver}:\n{pick(sols)}" for solver, (sols, _) in results.items()
                    if pick(sols) != ref]
            if diff:
                raise CheckError(f"{'optimal' if opt else 'first'} solution differs; JaCoP:\n"
                                 f"{ref}\n" + "\n".join(diff))
            summary = "the same optimal solution" if opt else "the same first solution"

        # feed JaCoP's solutions back to Gecode as data fixing the output variables
        sols_to_check = jacop[-1:] if opt else jacop
        step = max(1, len(sols_to_check) // FEASIBILITY_CHECKS)
        checked = 0
        names = {m.group(3) for m in DECLARATION.finditer(strip_comments(text))}
        names -= set(re.findall(r"(?m)^\s*(\w+)\s*=", strip_comments(text)))
        for i, sol in enumerate(sols_to_check[::step][:FEASIBILITY_CHECKS]):
            dzn = os.path.join(work, f"sol{i}.dzn")
            with open(dzn, "w") as f:
                # only variables without a right-hand side can be given as data
                for item in re.split(r";\s*\n", sol + "\n"):
                    m = re.match(r"\s*(\w+)\s*=", item)
                    if m and m.group(1) in names:
                        f.write(item.strip() + ";\n")
            try:
                sols, _, _ = solve_with(checker, mzn, False, dzn)
            except CheckError as e:
                raise CheckError(f"{checker} rejects JaCoP solution {i}:\n{sol}\n{e}")
            if not sols:
                raise CheckError(f"{checker} rejects JaCoP solution {i}:\n{sol}")
            checked += 1

        mode = "all" if all_mode else "fixed"
        names = " and ".join(solver_version(x) for x in solvers)
        lines = [f"mode: {mode} ({'optimisation' if opt else 'satisfaction'})",
                 f"verified: JaCoP, {names} find {summary}",
                 f"feasibility: {checked} JaCoP solution(s) accepted by {checker} as data"]
        if gecode_differs:
            lines.append(GECODE_DIFFERS + gecode_differs)
        return "\n".join(lines) + "\n"
    finally:
        shutil.rmtree(work, ignore_errors=True)


def add(args):
    src = args.model
    name = args.name or "hakank_" + os.path.splitext(os.path.basename(src))[0]
    test_dir = os.path.join(FZ_ROOT, args.category, name)
    if os.path.exists(test_dir):
        raise CheckError(f"{test_dir} exists")
    text = open(src).read()
    for inc in re.findall(r'(?m)^\s*include\s+"([^"]+)"', strip_comments(text)):
        if os.path.exists(os.path.join(os.path.dirname(src), inc)):
            raise CheckError(f"model includes the local file {inc}")
    opt = is_optimisation(text)
    mode = args.mode
    if mode == "auto":
        mode = "fixed" if opt else "all"
        if mode == "all":
            try:
                sols, complete, _ = solve_with("gecode", src, True, timeout=20)
                if not complete or len(sols) > MAX_ALL:
                    mode = "fixed"
            except CheckError:
                mode = "fixed"
    if mode == "all" and opt:
        raise CheckError("mode all is for satisfaction models")
    source = args.source or os.path.basename(src)
    if args.origin:
        header = f"% Cross-checked regression test, {args.origin}.\n"
        source_line = f"source: {args.origin}\n"
    else:
        header = (f"% Cross-checked regression test, from Hakan Kjellerstrand's {source}"
                  f"\n% (https://github.com/radsz/hakank/tree/master/minizinc).\n")
        source_line = f"source: hakank/minizinc/{source}\n"
    if args.note:
        header += f"% {args.note}\n"
    if mode == "fixed":
        text = fix_search(text)
        header += ("% Search annotation made input_order/indomain_min on all decision variables, so"
                   "\n% every solver reaches the same solution.\n")
    os.makedirs(test_dir)
    try:
        mzn = os.path.join(test_dir, name + ".mzn")
        with open(mzn, "w") as f:
            f.write(header + text)
        if mode == "all":
            with open(os.path.join(test_dir, "options.opt"), "w") as f:
                f.write("\n".join(ALL_SOLUTIONS) + "\n")
        fzn = os.path.join(test_dir, name + ".fzn")
        ozn = os.path.join(test_dir, name + ".ozn")
        compile_jacop(mzn, fzn, ozn)
        os.remove(ozn)
        t = golden(fzn, os.path.join(test_dir, name + ".out"), mode == "all")
        if t > MAX_JACOP_SECONDS:
            raise CheckError(f"JaCoP needs {t:.1f}s, more than {MAX_JACOP_SECONDS}s")
        report = verify(test_dir, args.gecode_differs)
        with open(os.path.join(test_dir, "crosscheck.txt"), "w") as f:
            f.write(source_line + report)
        write_metadata(test_dir, fzn)
        print(f"added {args.category}/{name}/{name}: {report.splitlines()[1]} ({t:.1f}s)")
    except BaseException:
        shutil.rmtree(test_dir, ignore_errors=True)
        raise


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("add")
    a.add_argument("model")
    a.add_argument("--mode", choices=("auto", "all", "fixed"), default="auto")
    a.add_argument("--name")
    a.add_argument("--category", default="upTo5sec")
    a.add_argument("--source", help="hakank model a variant was derived from")
    a.add_argument("--note", help="one line saying how the model differs from its source")
    a.add_argument("--origin", help="where a model that is not from hakank comes from")
    a.add_argument("--gecode-differs", metavar="REASON",
                   help="Gecode departs from the MiniZinc library here; verify with Chuffed only")
    v = sub.add_parser("verify")
    v.add_argument("dirs", nargs="+")
    args = ap.parse_args()
    failed = 0
    if args.cmd == "add":
        try:
            add(args)
        except CheckError as e:
            print(f"rejected {args.model}: {e}")
            failed = 1
    else:
        for d in args.dirs:
            try:
                report = verify(d)
                print(f"ok {d}: {report.splitlines()[1]}")
            except CheckError as e:
                print(f"FAILED {d}: {e}")
                failed += 1
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
