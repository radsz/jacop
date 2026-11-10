"""Random variants of the suite's small models: each var domain lo..hi gets a new upper bound
hi + d (d in -1..1, never below lo), from seed 11 on constants of constraints move by one too,
from seed 68 on lower bounds move by -1..1 as well and so do the values of constant arrays,
from seed 141 on a comparison of a constraint line may change into another (<=, <, >=, >, =, !=),
flattened with JaCoP's and MiniZinc's std library.
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
        if seed >= 68:
            lo += rnd.randint(-1, 1)
        return f'{mt.group(1)}{lo}..{max(lo, hi + rnd.randint(-1, 1))}'
    new = dom.sub(change, src)
    if seed >= 11:
        # from seed 11 on, also move constants of constraints by one (not ranges or indices)
        def nudge(mt):
            v = int(mt.group(0))
            return str(max(0, v + rnd.choice([-1, 1]))) if rnd.random() < 0.3 else mt.group(0)
        new = '\n'.join(re.sub(r'(?<![\w.\[])\d+(?![\w.\]])', nudge, l) if l.startswith('constraint') else l
                        for l in new.split('\n'))
    if seed >= 68:
        # from seed 68 on, also move the values of constant int arrays (durations, weights, tables)
        def nudge_values(l):
            if not re.match(r'array\[[^]]*\] of int: *\w+ *=', l):
                return l
            head, _, body = l.partition('=')
            return head + '=' + re.sub(r'(?<![\w.])\d+(?![\w.])', nudge, body)
        new = '\n'.join(nudge_values(l) for l in new.split('\n'))
    if seed >= 141:
        # from seed 141 on, a comparison in a constraint line may become another one
        ops = ['<=', '<', '>=', '>', '=', '!=']
        def swap(mt):
            return f' {rnd.choice(ops)} ' if rnd.random() < 0.3 else mt.group(0)
        new = '\n'.join(re.sub(r' (<=|>=|!=|<|>|=) ', swap, l) if l.startswith('constraint') else l
                        for l in new.split('\n'))
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
