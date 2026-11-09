"""Random variants of the suite's small models: each var domain lo..hi gets a new upper bound
hi + d (d in -1..1, never below lo), flattened with JaCoP's and MiniZinc's std library.
Usage: MZN=minizinc MZN_SOLVER_PATH=... gen_variants.py SEED COUNT OUTDIR, then run
AllSolutionsSuite with -Dsuite.roots=gen=OUTDIR (see decomposition/README.md)."""
import os, random, re, subprocess, sys
A = os.path.dirname(os.path.abspath(__file__))
MZN = os.environ.get('MZN', 'minizinc')
env = dict(os.environ)
seed, count, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
rnd = random.Random(seed)
models = sorted(f[:-4] for f in os.listdir(A + '/models') if f.endswith('.mzn'))
models = [m for m in models if not os.path.exists(f'{A}/models/{m}.no-std')]
dom = re.compile(r'(var (?:opt )?)(-?\d+)\.\.(-?\d+)')
made = 0
for k in range(count * 3):
    if made >= count:
        break
    m = rnd.choice(models)
    src = open(f'{A}/models/{m}.mzn').read()
    def change(mt):
        lo, hi = int(mt.group(2)), int(mt.group(3))
        return f'{mt.group(1)}{lo}..{max(lo, hi + rnd.randint(-1, 1))}'
    new = dom.sub(change, src)
    if new == src:
        continue
    name = f'{m}_s{seed}_{k}'
    d = f'{out}/{name}'
    os.makedirs(d, exist_ok=True)
    open(f'{d}/{name}.mzn', 'w').write(new)
    flags = open(f'{A}/models/{m}.jacop-flags').read().split() if os.path.exists(f'{A}/models/{m}.jacop-flags') else []
    ok = subprocess.run([MZN, '-c', '--solver', 'org.jacop', *flags, f'{d}/{name}.mzn', '--fzn', f'{d}/{name}.fzn', '--no-output-ozn'], env=env, capture_output=True).returncode == 0
    ok = ok and subprocess.run([MZN, '-c', '--solver', 'org.std', '-I', f'{A}/shims', f'{d}/{name}.mzn', '--fzn', f'{d}/{name}.std.fzn', '--no-output-ozn'], env=env, capture_output=True).returncode == 0
    if ok:
        made += 1
    else:
        subprocess.run(['rm', '-rf', d])
print(made)
