#!/usr/bin/env python3
"""Runs the Geost benchmarks (org.jacop.geost.GeostBenchmark) on two builds and compares them.

Typical use, from the repository root, to check a change against develop-5.0:

    scripts/geost-benchmarks.py run --baseline develop-5.0 --limit 60 --repeat 3

It builds jacop-core of the baseline ref in a temporary git worktree, compiles the benchmark
sources of this working tree against both builds, runs the benchmarks on each and prints one line
per benchmark and model with the failures, nodes and time of both and their ratios. Results are
kept as JSON lines (--out-dir) so they can be compared again later:

    scripts/geost-benchmarks.py compare base.jsonl new.jsonl

A run whose status, solution count or checks differ between the builds is flagged; that is a
correctness problem, not a performance one. Time ratios below 0.9 or above 1.1 are marked, but
only compare times measured on the same machine in the same session.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCES = ["GeostBenchmark.java", "GeostInstance.java", "GeostInstanceGenerator.java"]
SRC_DIR = os.path.join(ROOT, "jacop-core", "src", "test", "java", "org", "jacop", "geost")


def sh(cmd, cwd=None, capture=False):
    print("+ " + " ".join(cmd), file=sys.stderr)
    if capture:
        return subprocess.run(cmd, cwd=cwd, check=True, capture_output=True, text=True).stdout
    subprocess.run(cmd, cwd=cwd, check=True)
    return None


def dependency_classpath():
    """The runtime classpath of jacop-core (slf4j and friends), from Maven."""
    if os.environ.get("GEOST_BENCH_CP"):
        return os.environ["GEOST_BENCH_CP"]
    out = os.path.join(tempfile.mkdtemp(), "cp.txt")
    sh(["mvn", "-q", "-pl", "jacop-core", "dependency:build-classpath",
        "-Dmdep.outputFile=" + out], cwd=ROOT)
    with open(out) as f:
        return f.read().strip()


def build(tree, java_opts):
    """Compiles jacop-core of a tree and the benchmark sources of this tree against it."""
    sh(["mvn", "-q", "-Pmin", "-pl", "jacop-core", "-DskipTests", "compile"], cwd=tree)
    classes = os.path.join(tree, "jacop-core", "target", "classes")
    bench = tempfile.mkdtemp(prefix="geost-bench-")
    sh(["javac", *java_opts, "-nowarn", "-cp", classes + os.pathsep + DEPS, "-d", bench,
        *[os.path.join(SRC_DIR, s) for s in SOURCES]])
    return classes + os.pathsep + bench + os.pathsep + DEPS


def run(classpath, label, out, args, java_opts):
    cmd = ["java", *java_opts, "-cp", classpath, "org.jacop.geost.GeostBenchmark",
           "--label", label, "--out", out, *args]
    # a non-zero exit means a failed check; the comparison reports it
    print("+ " + " ".join(cmd), file=sys.stderr)
    subprocess.run(cmd)


def load(path):
    with open(path) as f:
        return {(r["bench"], r["model"]): r for r in map(json.loads, f)}


def ratio(a, b):
    if a == 0:
        return "-" if b == 0 else "inf"
    return "%.2f" % (b / a)


def compare(base_path, new_path):
    base, new = load(base_path), load(new_path)
    bad = 0
    print("%-22s %-14s %-24s %-24s %6s %6s" % ("bench", "model", "baseline", "candidate",
                                                 "fails", "time"))
    for key in sorted(set(base) | set(new), key=lambda k: (k[0], k[1])):
        a, b = base.get(key), new.get(key)
        if a is None or b is None:
            print("%-22s %-14s missing in %s" % (key[0], key[1], "baseline" if a is None else
                                                  "candidate"))
            continue
        flag = ""
        done = a["status"] != "LIMIT" and b["status"] != "LIMIT"
        if not a["ok"] or not b["ok"]:
            flag = "  CHECK FAILED " + (a["note"] or b["note"])
        elif done and (a["status"] != b["status"]
                       or (a["status"] == "ALL" and a["solutions"] != b["solutions"])):
            flag = "  RESULT DIFFERS"
        if flag:
            bad += 1
        fmt = lambda r: "%s f=%d %dms" % (r["status"], r["fails"], r["ms"])
        if done:
            fr, tr = ratio(a["fails"], b["fails"]), ratio(a["ms"], b["ms"])
        else:
            # time-limited: compare the nodes explored per second instead
            fr = "-"
            tr = ratio(b["nodes"] / max(b["ms"], 1), a["nodes"] / max(a["ms"], 1))
        mark = ""
        try:
            t = float(tr)
            mark = " +" if t < 0.9 else " -" if t > 1.1 else ""
        except ValueError:
            pass
        print("%-22s %-14s %-24s %-24s %6s %6s%s%s" % (key[0], key[1], fmt(a), fmt(b), fr, tr,
                                                       mark, flag))
    print("\nratios are candidate / baseline; '+' marks a candidate at least 10% faster, '-' 10% "
          "slower; for time-limited runs the time ratio is the inverse ratio of nodes per second")
    return bad


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--baseline", default="develop-5.0", help="git ref to compare with")
    r.add_argument("--limit", default="60", help="seconds per run")
    r.add_argument("--repeat", default="1", help="runs per benchmark, the fastest is kept")
    r.add_argument("--filter", default=".*", help="regex on benchmark names")
    r.add_argument("--models", default=None, help="for example geost,diffn")
    r.add_argument("--out-dir", default=".", help="where the JSON lines go")
    r.add_argument("--java-opt", action="append", default=[],
                   help="extra javac/java option, e.g. --enable-preview")
    c = sub.add_parser("compare")
    c.add_argument("baseline")
    c.add_argument("candidate")
    a = p.parse_args()
    if a.cmd == "compare":
        sys.exit(1 if compare(a.baseline, a.candidate) else 0)

    global DEPS
    DEPS = dependency_classpath()
    args = ["--limit", a.limit, "--repeat", a.repeat, "--filter", a.filter]
    if a.models:
        args += ["--models", a.models]
    work = tempfile.mkdtemp(prefix="geost-baseline-")
    sh(["git", "worktree", "add", "--detach", work, a.baseline], cwd=ROOT)
    try:
        base_cp = build(work, a.java_opt)
        new_cp = build(ROOT, a.java_opt)
        base_out = os.path.join(a.out_dir, "geost-bench-baseline.jsonl")
        new_out = os.path.join(a.out_dir, "geost-bench-candidate.jsonl")
        run(base_cp, a.baseline, base_out, args, a.java_opt)
        run(new_cp, "working-tree", new_out, args, a.java_opt)
    finally:
        sh(["git", "worktree", "remove", "--force", work], cwd=ROOT)
        shutil.rmtree(work, ignore_errors=True)
    sys.exit(1 if compare(base_out, new_out) else 0)


DEPS = ""

if __name__ == "__main__":
    main()
