"""Second stage of the search for a law: the deeper search of law_deep (C++).

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
of the author, who is responsible for its content.

It starts from a law found by the first stage (../law_cg.py), keeps the linear programme as
there, and in every round runs one chain of law_deep from each configuration in use: the chain
changes which points are double, relaxes the positions after every change, and returns its best
configurations. Those of negative reduced cost (recomputed here) are added to the programme.

The log compares the share of simple points with the value 0.68182868746... recorded for the law
of Alpöge and Furman. Like the first stage this is a heuristic in floating point; the law it
ends with is certified afterwards by ../law_certify.py and ../law_check_iv.py.

usage: law_deep.py law_in.json rounds out.json [threads [steps [keep [temperature [seed]]]]]
"""
import sys, os, json, time, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np
from law_lp import features, GAP_MIN
from law_cg import RestrictedProgramme, normalise, dump

BINARY = os.path.join(HERE, 'build', 'law_deep')
ACCEPT = -1e-9
P0_AF = 0.68182868746


def deep(lp, starts, threads, steps, keep, temperature, seed, iters=300):
    """one chain of law_deep from each start; returns the configurations kept, as (cost, x, d)"""
    N = lp.N; starts = [normalise(x, d, N) for x, d in starts]
    with tempfile.TemporaryDirectory() as td:
        fin, fout = os.path.join(td, 'in.txt'), os.path.join(td, 'out.txt')
        with open(fin, 'w') as fh:
            fh.write(f'{N} {GAP_MIN!r} {iters} {len(starts)} {steps} {keep} {temperature!r} {seed}\n')
            fh.write(' '.join(repr(float(v)) for v in lp.y[:-1]) + '\n')
            for x, d in starts:
                fh.write(f'{len(x)}\n' + ' '.join(repr(float(v)) for v in x) + '\n' + ' '.join(str(int(round(v))) for v in d) + '\n')
        subprocess.run([BINARY, fin, fout], check=True, env=dict(os.environ, OMP_NUM_THREADS=str(threads)))
        out = []
        with open(fout) as fh:
            for _ in starts:
                for _ in range(int(fh.readline())):
                    cost, n = fh.readline().split()
                    x = np.array(fh.readline().split(), float); d = np.array(fh.readline().split(), float)
                    assert int(n) == len(x) == len(d) and abs(d.sum() - N) < 1e-9
                    out.append((float(cost), x, d))
    return out


def run(law_in, rounds, out, threads=9, steps=20, keep=4, temperature=1e-4, seed=1, log=print):
    W = json.load(open(law_in)); N = W['N']; lp = RestrictedProgramme(N); t0 = time.time()
    for c in W['law']:
        lp.add(np.array(c['x']), np.array(c['d'], float))
    p = lp.solve(); p_start = p
    log(f'N = {N}: start from {os.path.basename(law_in)} with {len(lp.cols)} configurations, p = {p:.10f}; '
        f'chains of {steps} steps, temperature {temperature:g}, {keep} kept per chain')
    meta = dict(program='law_deep.py', start=os.path.basename(law_in), steps=steps, keep=keep, temperature=temperature, seed=seed)
    for it in range(rounds):
        supp = [(c['x'], c['d']) for c, w in zip(lp.cols, lp.w) if w > 1e-9]
        t1 = time.time(); res = deep(lp, supp, threads, steps, keep, temperature, seed * 1000003 + it); t_deep = time.time() - t1
        added = 0; best = 0.0; seen = set(); worst_gap = 0.0
        for cost, x, d in res:
            v = features(x, d, N); n1 = float((d == 1).sum()); rc = lp.reduced(v, n1)     # recomputed here
            worst_gap = max(worst_gap, abs(rc - (cost - lp.y[-1])))
            best = min(best, rc); key = (len(x), round(rc, 10))
            if rc < ACCEPT and key not in seen:
                seen.add(key); lp.add(x, d, v); added += 1
        assert worst_gap < 1e-7, f'cost of law_deep and reduced cost recomputed in Python differ by {worst_gap}'
        lp.prune(limit=12 * N, keep=8 * N)
        t1 = time.time(); p = lp.solve(); t_lp = time.time() - t1
        log(f'round {it}: p = {p:.10f}  gain since start {p_start - p:.2e}  p - p0(AF) = {p - P0_AF:+.2e}  '
            f'returned {len(res)}, added {added}, best reduced cost {best:.2e}, columns {len(lp.cols)}'
            f'  [search {t_deep:.1f} s, LP {t_lp:.1f} s, total {time.time() - t0:.0f} s]')
        if it % 10 == 9:
            dump(lp, out, dict(meta, rounds=it + 1, finished=False))
    law = dump(lp, out, dict(meta, rounds=rounds, finished=True))
    log(f'finished: p = {lp.p:.10f}, {len(law)} basic configurations')


if __name__ == '__main__':
    a = sys.argv
    run(a[1], int(a[2]), a[3], threads=int(a[4]) if len(a) > 4 else 9, steps=int(a[5]) if len(a) > 5 else 20,
        keep=int(a[6]) if len(a) > 6 else 4, temperature=float(a[7]) if len(a) > 7 else 1e-4,
        seed=int(a[8]) if len(a) > 8 else 1, log=lambda s: print(s, flush=True))
