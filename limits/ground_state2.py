# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
"""Variational ceilings, second version: lattice-gas trial states (floating point, not a proof).

Trial states are periodic site sequences over {S, D, V} (simple point, double point, vacancy)
on the unit lattice, relaxed by continuous optimisation of the gaps.  Column generation:
for the current certificate (x, y, b) rank all sequences by unrelaxed slack, relax the worst
ones, add them to the LP, repeat.  See ground_state.py for the LP and the energy formula.

usage: ground_state2.py [window] [max sites] [range] [outfile.json]
"""
import sys, json, itertools, os, glob
import numpy as np
from scipy.optimize import minimize
from ground_state import Win, energy_full, energy_range, solve_lp


def necklaces(n):
    seen = set()
    for seq in itertools.product('SDV', repeat=n):
        if 'S' not in seq and 'D' not in seq:
            continue
        if seq[0] == 'V':
            continue
        rots = [seq[i:] + seq[:i] for i in range(n)]
        rots += [tuple(reversed(r)) for r in rots]
        can = min(rots)
        if can in seen:
            continue
        seen.add(can)
        yield seq


def to_state(seq):
    """site sequence -> (labels, gaps) of the periodic configuration on the unit lattice"""
    n = len(seq)
    idx = [i for i, s in enumerate(seq) if s != 'V']
    labs = [1 if seq[i] == 'S' else 2 for i in idx]
    gaps = [((idx[(k + 1) % len(idx)] - idx[k] - 1) % n) + 1 for k in range(len(idx))]
    return labs, gaps


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else 'new'
    maxn = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    rng = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    out = sys.argv[4] if len(sys.argv) > 4 else None
    win = Win(name)
    en = (lambda g, l: energy_full(win, g, l)) if rng == 0 else (lambda g, l: energy_range(win, g, l, rng))
    cands = []
    for n in range(1, maxn + 1):
        for seq in necklaces(n):
            labs, gaps = to_state(seq)
            if rng and len(labs) <= 0:
                continue
            cands.append((labs, np.array(gaps, float)))
    # unrelaxed energies
    E0 = np.array([en(g, l) for l, g in cands])
    n1 = np.array([sum(1 for a in l if a == 1) for l, g in cands], float)
    n2 = np.array([sum(1 for a in l if a == 2) for l, g in cands], float)
    P0 = np.array([g.sum() for l, g in cands])
    print(f'window {name}: C = {win.C:.12f}, baseline {(3 - win.C) / 2:.6f}, range {"all" if rng == 0 else rng}, '
          f'{len(cands)} site sequences up to {maxn} sites', flush=True)
    states = [(n1[i], n2[i], P0[i], E0[i]) for i in range(len(cands))]
    desc = [(tuple(cands[i][0]), tuple(cands[i][1])) for i in range(len(cands))]
    relaxed = {}
    # seed with binding states of earlier runs for the same window and range
    for fn in glob.glob(f'gs2_{name}_n*_r{rng}.json'):
        for st in json.load(open(fn))['binding']:
            labs = st['labels']; g = np.array(st['gaps'])
            states.append((sum(1 for a in labs if a == 1), sum(1 for a in labs if a == 2), float(g.sum()), en(g, labs)))
            desc.append((tuple(labs), tuple(float(v) for v in g)))
    for it in range(30):
        Q, sol = solve_lp(win, states)
        x, y, b = sol
        slack0 = E0 - (x * n1 + y * n2 - b * P0)
        order = np.argsort(slack0)[:int(os.environ.get('TOPK', '60'))]
        nadd = 0; worst = 0.0
        for i in order:
            labs, g0 = cands[i]
            m1, m2 = n1[i], n2[i]
            def slack(g):
                g = np.abs(g) + 1e-3
                return en(g, labs) - (x * m1 + y * m2 - b * g.sum())
            starts = [g0]
            if i in relaxed:
                starts.append(relaxed[i])
            best = None
            for s in starts:
                r = minimize(slack, s, method='L-BFGS-B', options=dict(maxiter=500, ftol=1e-15, gtol=1e-10))
                r2 = minimize(slack, r.x, method='Nelder-Mead', options=dict(xatol=1e-8, fatol=1e-13, maxiter=3000))
                if r2.fun < r.fun:
                    r = r2
                if best is None or r.fun < best.fun:
                    best = r
            g = np.abs(best.x) + 1e-3
            relaxed[i] = g
            worst = min(worst, best.fun)
            if best.fun < -1e-10:
                states.append((m1, m2, float(g.sum()), en(g, labs)))
                desc.append((tuple(labs), tuple(float(v) for v in g)))
                nadd += 1
        print(f'iter {it}: Q <= {Q:.6f} at (x, y, b) = ({x:.5f}, {y:.5f}, {b:.5f}); worst slack {worst:.2e}, added {nadd}',
              flush=True)
        if nadd == 0:
            break
    Q, sol = solve_lp(win, states)
    x, y, b = sol
    print(f'CEILING {name} range {"all" if rng == 0 else rng}: Q <= {Q:.6f} at (x, y, b) = ({x:.6f}, {y:.6f}, {b:.6f})')
    binding = []
    for (m1, m2, P, E), (lab, gaps) in zip(states, desc):
        if E - (x * m1 + y * m2 - b * P) < 1e-8:
            binding.append(dict(labels=list(lab), gaps=[float(v) for v in gaps], P=float(P), E=float(E)))
            print('   binding: labels', lab, 'gaps', tuple(round(float(v), 5) for v in gaps), 'P', round(float(P), 5),
                  'E', round(float(E), 6))
    if out:
        json.dump(dict(window=name, range=rng, maxsites=maxn, Q=Q, x=x, y=y, b=b, C=win.C, binding=binding),
                  open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
