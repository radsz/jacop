#!/usr/bin/env python3
"""Flattens the MiniZinc sources of benchmark FlatZinc files with MiniZinc's standard library.

AllSolutionsSuite compares a FlatZinc file <root>/<rel>.fzn with its twin
<twins>/<name>/<rel>.std.fzn (suite.twins): the same model and data flattened without JaCoP's
library, so that every global constraint is decomposed by MiniZinc. The source of a file is found
next to it (one .mzn in the directory, and a .dzn named like the instance), or for the Challenge
bench in its instances.tsv.

usage: make_twins.py TWINS NAME=ROOT[:mznc] ... [--max-bytes N] [--jobs N]
env: MZN (minizinc), MZN_SOLVER_PATH with a solver org.std whose mznlib is an empty directory.
"""
import argparse, concurrent.futures, csv, gzip, os, subprocess, sys

MZN = os.environ.get("MZN", "minizinc")
SHIMS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "shims")


def sources(name, root, mznc):
    """Yields (relative fzn name without extension, fzn path, mzn, dzn or None)."""
    if mznc:
        repo = os.path.dirname(os.path.abspath(root))
        inst = {}
        with open(os.path.join(repo, "instances.tsv")) as f:
            for row in csv.DictReader(f, delimiter="\t"):
                inst[row["id"]] = row
        for dirpath, _, files in os.walk(root):
            for fn in files:
                if not fn.endswith(".fzn.gz"):
                    continue
                p = os.path.join(dirpath, fn)
                rel = os.path.relpath(p, root)[: -len(".fzn.gz")]
                row = inst.get(rel.split("/", 1)[1]) if "/" in rel else None
                if row:
                    mzn = os.path.join(repo, "mzn", row["model"])
                    dzn = os.path.join(repo, "mzn", row["data"]) if row["data"] else None
                    yield rel, p, mzn, dzn
        return
    for dirpath, _, files in os.walk(root):
        mzns = [f for f in files if f.endswith(".mzn")]
        for fn in files:
            if not fn.endswith(".fzn") or fn.endswith(".std.fzn"):
                continue
            stem = fn[:-4]
            p = os.path.join(dirpath, fn)
            rel = os.path.relpath(p, root)[:-4]
            if stem + ".mzn" in mzns:
                yield rel, p, os.path.join(dirpath, stem + ".mzn"), None
            elif len(mzns) == 1:
                dzn = os.path.join(dirpath, stem + ".dzn")
                json = os.path.join(dirpath, stem + ".json")
                data = dzn if os.path.exists(dzn) else json if os.path.exists(json) else None
                yield rel, p, os.path.join(dirpath, mzns[0]), data


def flatten(job):
    out, mzn, dzn = job
    os.makedirs(os.path.dirname(out), exist_ok=True)
    cmd = [MZN, "-c", "--solver", "org.std", "-I", SHIMS, mzn] + ([dzn] if dzn else [])
    cmd += ["--fzn", out + ".tmp", "--no-output-ozn"]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                           cwd=os.path.dirname(mzn))
    except subprocess.TimeoutExpired:
        return out, "timeout"
    if r.returncode != 0:
        if os.path.exists(out + ".tmp"):
            os.remove(out + ".tmp")
        return out, "error " + (r.stderr.strip().splitlines() or [""])[0][:200]
    os.replace(out + ".tmp", out)
    return out, "ok"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("twins")
    ap.add_argument("roots", nargs="+")
    ap.add_argument("--max-bytes", type=int, default=1000000)
    ap.add_argument("--jobs", type=int, default=2)
    a = ap.parse_args()
    jobs = []
    for spec in a.roots:
        name, root = spec.split("=", 1)
        mznc = root.endswith(":mznc")
        root = root[:-5] if mznc else root
        for rel, p, mzn, dzn in sources(name, root, mznc):
            size = os.path.getsize(p) * (8 if p.endswith(".gz") else 1)
            out = os.path.join(a.twins, name, rel + ".std.fzn")
            if size <= a.max_bytes and os.path.exists(mzn) and not os.path.exists(out):
                jobs.append((out, mzn, dzn))
    print(len(jobs), "to flatten", flush=True)
    stats = {}
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as ex:
        for out, status in ex.map(flatten, jobs):
            key = status.split()[0]
            stats[key] = stats.get(key, 0) + 1
            if key != "ok":
                print(out, status, flush=True)
    print(stats)


if __name__ == "__main__":
    main()
