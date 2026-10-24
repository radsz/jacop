#!/usr/bin/env python3
"""Differential testing of JaCoP's MiniZinc globals.

Generates small random MiniZinc models, one global constraint each (sometimes reified), with
domains that have holes, constants and repeated variables, and compares all solutions found by
JaCoP with those of a reference solver that uses the decompositions of the MiniZinc standard
library. Every model whose solution sets differ is printed.

Requirements: MiniZinc on the PATH (or in the MINIZINC environment variable) with the JaCoP
solver configuration (org.jacop) installed, and Chuffed, which comes with the MiniZinc bundle.

usage: python3 scripts/minizinc-differential.py <seed> <models-per-global> [global,...]
"""
import concurrent.futures as cf
import os
import random
import subprocess
import sys
import tempfile

MZN = os.environ.get("MINIZINC", "minizinc")
REFERENCE = ["--solver", "chuffed", "-G", "std"]
WORK = tempfile.mkdtemp(prefix="minizinc-differential-")


class Model:
    def __init__(self, r):
        self.r = r
        self.decls = []
        self.n = 0

    def var(self, lo, hi, holes=True):
        vals = [v for v in range(lo, hi + 1) if not holes or self.r.random() < 0.75]
        if not vals:
            vals = [self.r.randint(lo, hi)]
        self.n += 1
        name = f"v{self.n}"
        self.decls.append(f"var {{{','.join(map(str, vals))}}}: {name};")
        return name

    def bvar(self):
        self.n += 1
        name = f"b{self.n}"
        self.decls.append(f"var bool: {name};")
        return name

    def arr(self, k, lo, hi, const=0.15, dup=0.1):
        """array literal of k entries: fresh variables, sometimes constants or repeated variables"""
        out = []
        for _ in range(k):
            p = self.r.random()
            if p < const:
                out.append(str(self.r.randint(lo, hi)))
            elif p < const + dup and any(not e.lstrip("-").isdigit() for e in out):
                out.append(self.r.choice([e for e in out if not e.lstrip("-").isdigit()]))
            else:
                out.append(self.var(lo, hi))
        return "[" + ",".join(out) + "]"

    def bvars(self, k):
        return "[" + ",".join(self.bvar() for _ in range(k)) + "]"

    def iset(self, lo, hi):
        vals = sorted(set(self.r.randint(lo, hi) for _ in range(self.r.randint(0, 3))))
        return "{" + ",".join(map(str, vals)) + "}"

    def ints(self, k, lo, hi):
        return "[" + ",".join(str(self.r.randint(lo, hi)) for _ in range(k)) + "]"


def reif(m, c):
    """sometimes reify the constraint"""
    p = m.r.random()
    if p < 0.6:
        return c
    b = m.bvar()
    return f"{b} <-> {c}" if p < 0.85 else f"{b} -> {c}"


CASES = {}


def case(name, reifiable=False):
    def deco(f):
        CASES[name] = (f, reifiable)
        return f
    return deco


R = lambda m: m.r.randint


@case("all_different", True)
def _(m): return f"all_different({m.arr(R(m)(1, 4), 0, 3)})"
@case("alldifferent_except_0", True)
def _(m): return f"alldifferent_except_0({m.arr(R(m)(1, 4), 0, 3)})"
@case("alldifferent_except", True)
def _(m): return f"alldifferent_except({m.arr(R(m)(1, 4), 0, 3)}, {m.iset(0, 3)})"
@case("all_equal", True)
def _(m): return f"all_equal({m.arr(R(m)(1, 4), 0, 2)})"
@case("among", True)
def _(m): return f"among({m.var(0, 4)}, {m.arr(R(m)(1, 4), 0, 3)}, {m.iset(0, 3)})"
@case("at_least", True)
def _(m): return f"at_least({R(m)(0, 3)}, {m.arr(R(m)(1, 4), 0, 2)}, {R(m)(0, 2)})"
@case("at_most", True)
def _(m): return f"at_most({R(m)(0, 3)}, {m.arr(R(m)(1, 4), 0, 2)}, {R(m)(0, 2)})"
@case("exactly", True)
def _(m): return f"exactly({R(m)(0, 3)}, {m.arr(R(m)(1, 4), 0, 2)}, {R(m)(0, 2)})"
@case("count_eq", True)
def _(m):
    y = m.var(0, 2) if m.r.random() < 0.5 else str(R(m)(0, 2))
    c = m.var(0, 4) if m.r.random() < 0.7 else str(R(m)(0, 4))
    return f"count_eq({m.arr(R(m)(1, 4), 0, 2)}, {y}, {c})"
@case("count_rel", True)
def _(m):
    op = m.r.choice(["count_geq", "count_gt", "count_leq", "count_lt", "count_neq"])
    y = m.var(0, 2) if m.r.random() < 0.3 else str(R(m)(0, 2))
    c = m.var(0, 4) if m.r.random() < 0.3 else str(R(m)(0, 4))
    return f"{op}({m.arr(R(m)(1, 4), 0, 2)}, {y}, {c})"
@case("global_cardinality", True)
def _(m):
    # distinct cover values: the implied constraint of the standard library is wrong for repeats
    cover = sorted(set(R(m)(0, 3) for _ in range(R(m)(1, 3))))
    return f"global_cardinality({m.arr(R(m)(1, 4), 0, 3)}, {cover}, {m.arr(len(cover), 0, 3)})"
@case("global_cardinality_closed", True)
def _(m):
    vals = sorted(set(R(m)(0, 3) for _ in range(R(m)(1, 3))))
    return f"global_cardinality_closed({m.arr(R(m)(1, 4), 0, 3)}, [{','.join(map(str, vals))}], {m.arr(len(vals), 0, 3)})"
@case("global_cardinality_low_up", True)
def _(m):
    vals = sorted(set(R(m)(0, 3) for _ in range(R(m)(1, 3))))
    lb = [R(m)(0, 2) for _ in vals]
    ub = [l + R(m)(0, 2) for l in lb]
    return f"global_cardinality_low_up({m.arr(R(m)(1, 4), 0, 3)}, {vals}, {lb}, {ub})"
@case("global_cardinality_low_up_closed", True)
def _(m):
    vals = sorted(set(R(m)(0, 3) for _ in range(R(m)(1, 3))))
    lb = [R(m)(0, 2) for _ in vals]
    ub = [l + R(m)(0, 2) for l in lb]
    return f"global_cardinality_low_up_closed({m.arr(R(m)(1, 4), 0, 3)}, {vals}, {lb}, {ub})"
@case("nvalue", True)
def _(m): return f"nvalue({m.var(0, 4)}, {m.arr(R(m)(1, 4), 0, 3)})"
@case("increasing", True)
def _(m): return f"{m.r.choice(['increasing','decreasing','strictly_increasing','strictly_decreasing'])}({m.arr(R(m)(1, 4), 0, 3)})"
@case("increasing_bool")
def _(m): return f"{m.r.choice(['increasing','decreasing','strictly_increasing','strictly_decreasing'])}({m.bvars(R(m)(1, 3))})"
@case("lex", True)
def _(m):
    op = m.r.choice(["lex_less", "lex_lesseq"])
    return f"{op}({m.arr(R(m)(1, 3), 0, 2)}, {m.arr(R(m)(1, 3), 0, 2)})"
@case("lex_bool", True)
def _(m):
    op = m.r.choice(["lex_less", "lex_lesseq"])
    k = R(m)(1, 3)
    return f"{op}({m.bvars(k)}, {m.bvars(k)})"
@case("member", True)
def _(m):
    y = m.var(0, 3) if m.r.random() < 0.7 else str(R(m)(0, 3))
    return f"member({m.arr(R(m)(1, 4), 0, 3)}, {y})"
@case("member_bool", True)
def _(m): return f"member({m.bvars(R(m)(1, 3))}, {m.bvar()})"
@case("maximum")
def _(m):
    op = m.r.choice(["maximum", "minimum"])
    return f"{op}({m.var(0, 3)}, {m.arr(R(m)(1, 4), 0, 3)})"
@case("arg_max")
def _(m):
    op = m.r.choice(["arg_max", "arg_min"])
    return f"{m.var(0, 5)} = {op}({m.arr(R(m)(1, 4), 0, 3)})"
@case("arg_max_bool")
def _(m):
    op = m.r.choice(["arg_max", "arg_min"])
    return f"{m.var(0, 5)} = {op}({m.bvars(R(m)(1, 4))})"
@case("regular", True)
def _(m):
    q, s = R(m)(1, 3), 2
    d = [[R(m)(0, q) for _ in range(s)] for _ in range(q)]
    fin = sorted(set(R(m)(1, q) for _ in range(R(m)(1, q))))
    rows = "|".join(",".join(map(str, row)) for row in d)
    return f"regular({m.arr(R(m)(1, 4), 1, 2)}, {q}, {s}, [|{rows}|], 1, {{{','.join(map(str, fin))}}})"
@case("cost_regular")
def _(m):
    q, s = R(m)(1, 3), R(m)(2, 3)
    d = [[R(m)(0, q) for _ in range(s)] for _ in range(q)]
    w = [[R(m)(-2, 4) for _ in range(s)] for _ in range(q)]
    fin = sorted(set(R(m)(1, q) for _ in range(R(m)(1, q))))
    rows = "|".join(",".join(map(str, row)) for row in d)
    costs = "|".join(",".join(map(str, row)) for row in w)
    k = R(m)(1, 4)
    return (f"cost_regular({m.arr(k, 1, s)}, {q}, {s}, [|{rows}|], 1, {{{','.join(map(str, fin))}}}, "
            f"[|{costs}|], {m.var(-3, 3 * k + 2)})")
@case("table", True)
def _(m):
    k, t = R(m)(1, 3), R(m)(0, 5)
    rows = "|".join(",".join(str(R(m)(0, 2)) for _ in range(k)) for _ in range(t))
    tab = f"[|{rows}|]" if t else f"array2d(1..0, 1..{k}, [])"
    return f"table({m.arr(k, 0, 2)}, {tab})"
@case("table_bool")
def _(m):
    k, t = R(m)(1, 3), R(m)(0, 4)
    rows = "|".join(",".join(m.r.choice(["true", "false"]) for _ in range(k)) for _ in range(t))
    tab = f"[|{rows}|]" if t else f"array2d(1..0, 1..{k}, [])"
    return f"table({m.bvars(k)}, {tab})"
@case("circuit")
def _(m):
    k = R(m)(1, 4)
    return f"circuit({m.arr(k, 1, k)})"
@case("subcircuit")
def _(m):
    k = R(m)(1, 4)
    return f"subcircuit({m.arr(k, 1, k)})"
@case("inverse")
def _(m):
    k = R(m)(1, 3)
    return f"inverse({m.arr(k, 1, k)}, {m.arr(k, 1, k)})"
@case("value_precede", True)
def _(m): return f"value_precede({R(m)(0, 2)}, {R(m)(0, 2)}, {m.arr(R(m)(1, 4), 0, 2)})"
@case("value_precede_chain")
def _(m): return f"value_precede_chain({m.ints(R(m)(0, 3), 0, 2)}, {m.arr(R(m)(1, 4), 0, 2)})"
@case("seq_precede_chain")
def _(m): return f"seq_precede_chain({m.arr(R(m)(1, 4), 0, 3)})"
@case("bin_packing")
def _(m):
    k = R(m)(1, 4)
    return f"bin_packing({R(m)(0, 4)}, {m.arr(k, 1, 3)}, {m.ints(k, 0, 3)})"
@case("bin_packing_capa")
def _(m):
    k, b = R(m)(1, 4), R(m)(1, 3)
    return f"bin_packing_capa({m.ints(b, 0, 4)}, {m.arr(k, 1, b)}, {m.ints(k, 0, 3)})"
@case("bin_packing_load")
def _(m):
    k, b = R(m)(1, 3), R(m)(1, 3)
    return f"bin_packing_load({m.arr(b, 0, 4)}, {m.arr(k, 1, b)}, {m.ints(k, 0, 3)})"
@case("knapsack")
def _(m):
    k = R(m)(1, 3)
    return f"knapsack({m.ints(k, 0, 3)}, {m.ints(k, 0, 3)}, {m.arr(k, 0, 2)}, {m.var(0, 8)}, {m.var(0, 8)})"
@case("diffn")
def _(m):
    k = R(m)(1, 3)
    op = m.r.choice(["diffn", "diffn_nonstrict"])
    return f"{op}({m.arr(k, 0, 2)}, {m.arr(k, 0, 2)}, {m.arr(k, 0, 2)}, {m.arr(k, 0, 2)})"
@case("disjunctive")
def _(m):
    k = R(m)(1, 3)
    op = m.r.choice(["disjunctive", "disjunctive_strict"])
    return f"{op}({m.arr(k, 0, 3)}, {m.arr(k, 0, 2)})"
@case("cumulative")
def _(m):
    k = R(m)(1, 3)
    b = m.var(0, 3) if m.r.random() < 0.5 else str(R(m)(0, 3))
    return f"cumulative({m.arr(k, 0, 3)}, {m.arr(k, 0, 2)}, {m.arr(k, 0, 3)}, {b})"
@case("distribute")
def _(m):
    k = R(m)(1, 3)
    return f"distribute({m.arr(k, 0, 3)}, {m.arr(k, 0, 2)}, {m.arr(R(m)(1, 3), 0, 2)})"
@case("element")
def _(m):
    k = R(m)(1, 4)
    return f"{m.var(0, 3)} = {m.arr(k, 0, 3)}[{m.var(0, k + 1)}]"
@case("int_set_channel")
def _(m):
    k = R(m)(1, 3)
    m.n += 1
    sname = f"s{m.n}"
    m.decls.append(f"array[1..{k}] of var set of 1..{k}: {sname};")
    return f"int_set_channel({m.arr(k, 1, k)}, {sname})"
@case("network_flow")
def _(m):
    nodes = R(m)(2, 3)
    arcs = [(R(m)(1, nodes), R(m)(1, nodes)) for _ in range(R(m)(1, 4))]
    arcs = [(a, b) for a, b in arcs if a != b] or [(1, 2)]
    bal = m.ints(nodes, -2, 2)
    rows = "|".join(f"{a},{b}" for a, b in arcs)
    return f"network_flow([|{rows}|], {bal}, {m.arr(len(arcs), 0, 2)})"
@case("network_flow_cost")
def _(m):
    nodes = R(m)(2, 3)
    arcs = [(R(m)(1, nodes), R(m)(1, nodes)) for _ in range(R(m)(1, 4))]
    arcs = [(a, b) for a, b in arcs if a != b] or [(1, 2)]
    bal = m.ints(nodes, -2, 2)
    rows = "|".join(f"{a},{b}" for a, b in arcs)
    return f"network_flow_cost([|{rows}|], {bal}, {m.ints(len(arcs), 0, 2)}, {m.arr(len(arcs), 0, 2)}, {m.var(0, 8)})"
@case("sliding_sum")
def _(m):
    lo = R(m)(0, 3)
    return f"sliding_sum({lo}, {lo + R(m)(0, 3)}, {R(m)(1, 3)}, {m.arr(R(m)(1, 4), 0, 2)})"


def make(name, r):
    m = Model(r)
    f, reifiable = CASES[name]
    c = f(m)
    if reifiable:
        c = reif(m, c)
    return 'include "globals.mzn";\n' + "\n".join(m.decls) + f"\nconstraint {c};\nsolve satisfy;\n"


def run(solver_args, path):
    p = subprocess.run([MZN, *solver_args, "-a", path], capture_output=True, text=True, timeout=120)
    out = p.stdout + p.stderr
    if "=====UNSATISFIABLE=====" in out:
        return frozenset(), out
    if "==========" not in out:
        return None, out
    sols, cur = [], []
    for line in p.stdout.splitlines():
        if line.strip() == "----------":
            sols.append("".join(sorted(cur)))
            cur = []
        elif line.strip() and not line.startswith("=") and not line.startswith("%"):
            cur.append(line.strip())
    return frozenset(sols), out


def trial(args):
    name, seed = args
    r = random.Random(seed)
    model = make(name, r)
    path = f"{WORK}/{name}_{seed}.mzn"
    open(path, "w").write(model)
    try:
        ref, refout = run(REFERENCE, path)
        got, gotout = run(["--solver", "org.jacop"], path)
    except subprocess.TimeoutExpired:
        return name, seed, "timeout", model, ""
    if ref is None:
        os.remove(path)
        return name, seed, "skip", model, refout[-300:]
    if got != ref:
        detail = gotout[-600:] if got is None else f"missing={sorted(ref - got)[:3]} wrong={sorted(got - ref)[:3]} jacop={len(got)} chuffed={len(ref)}"
        return name, seed, "MISMATCH", model, detail
    os.remove(path)
    return name, seed, "ok", model, ""


if __name__ == "__main__":
    seed0, trials = int(sys.argv[1]), int(sys.argv[2])
    names = sys.argv[3].split(",") if len(sys.argv) > 3 else list(CASES)
    jobs = [(n, seed0 * 100000 + i * 1000 + j) for i, n in enumerate(names) for j in range(trials)]
    stats = {}
    with cf.ThreadPoolExecutor(4) as ex:
        for name, seed, status, model, detail in ex.map(trial, jobs):
            stats.setdefault(name, {}).setdefault(status, 0)
            stats[name][status] += 1
            if status in ("MISMATCH", "timeout"):
                print(f"== {status} {name} seed={seed}\n{model}{detail}\n", flush=True)
    for n in names:
        print(f"{n:34s} {stats.get(n)}")
