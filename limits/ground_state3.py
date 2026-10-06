# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
"""Variational ceilings, third version: multi-start column generation (floating point).

Same model as ground_state2.py (periodic site sequences over {S, D, V}, gaps relaxed), but
  - R = f*f is tabulated once and interpolated by a cubic spline, so energies are fast;
  - every sequence is relaxed from several starts in every round (lattice start, the previous
    optimum, random perturbations), not only the sequences with the smallest unrelaxed slack.
The result is an upper bound for Q*(f) from the states found; certify with ceiling_certified.py.

usage: ground_state3.py window maxsites range nstarts out.json     (range 0 = all pairs)
"""
import sys, json, itertools
import numpy as np
from scipy.interpolate import CubicSpline
from scipy.optimize import minimize
from ground_state import Win, solve_lp
from ground_state2 import necklaces, to_state

name = sys.argv[1]; maxn = int(sys.argv[2]); rng_s = int(sys.argv[3]); nstarts = int(sys.argv[4]); out = sys.argv[5]
win = Win(name)
ug = np.linspace(0.0, 1.0, 4001)
Rs = CubicSpline(ug, np.array([win.R(u) for u in ug]))
R0 = float(Rs(0.0))

def energy_all(gaps, d):
    """pair energy per period, all pairs (Poisson formula)"""
    P = gaps.sum(); y = np.concatenate(([0.0], np.cumsum(gaps)[:-1]))
    M = int(np.floor(P))
    m = np.arange(1, M + 1)
    S = (d[None, :] * np.exp(2j * np.pi * np.outer(m, y) / P)).sum(axis=1)
    tot = R0 * d.sum() ** 2 + 2 * np.sum(Rs(m / P) * np.abs(S) ** 2)
    return tot / P - np.sum(d * d)

def energy_rng(gaps, d, s):
    p = len(d); tot = 0.0
    for i in range(p):
        dist = 0.0
        for r in range(1, s + 1):
            dist += gaps[(i + r - 1) % p]
            tot += 2 * d[i] * d[(i + r) % p] * float(win.K(dist)) ** 2
    return tot

en = (lambda g, d: energy_all(g, d)) if rng_s == 0 else (lambda g, d: energy_rng(g, d, rng_s))
gmin = 0.3 if rng_s == 0 else 0.85
gmax = 4.0      # gaps are kept bounded: an unbounded line search can reach periods of 10^7 and exhaust memory

cands = []
for n in range(1, maxn + 1):
    for seq in necklaces(n):
        labs, gaps = to_state(seq)
        cands.append((np.array(labs, float), np.array(gaps, float)))
print(f'window {name}: C = {win.C:.12f}, {len(cands)} sequences up to {maxn} sites, range {rng_s or "all"}, starts {nstarts}', flush=True)

states = []; desc = []
def add(d, g):
    n1 = float(np.sum(d == 1)); n2 = float(np.sum(d == 2))
    states.append((n1, n2, float(g.sum()), float(en(g, d))))
    desc.append(([int(v) for v in d], [float(v) for v in g]))
for d, g in cands:
    add(d, g)
# also uniform spacings for single-site states
for s in np.arange(0.86, 2.6, 0.02):
    add(np.array([1.0]), np.array([s])); add(np.array([2.0]), np.array([s]))

rs = np.random.default_rng(7)
best_g = {}
for it in range(25):
    Q, sol = solve_lp(win, states)
    x, y, b = sol
    nadd = 0; worst = 0.0
    for i, (d, g0) in enumerate(cands):
        n1 = np.sum(d == 1); n2 = np.sum(d == 2)
        def slack(g):
            g = np.clip(np.abs(g), gmin, gmax)
            return en(g, d) - (x * n1 + y * n2 - b * g.sum())
        starts = [g0]
        if i in best_g:
            starts.append(best_g[i])
        for _ in range(nstarts):
            starts.append(np.maximum(g0 + rs.normal(0, 0.12, len(g0)), gmin))
        best = None
        for s0 in starts:
            r = minimize(slack, np.clip(s0, gmin, gmax), method='L-BFGS-B', bounds=[(gmin, gmax)] * len(s0),
                         options=dict(maxiter=300))
            if best is None or r.fun < best.fun:
                best = r
        g = np.clip(np.abs(best.x), gmin, gmax)
        best_g[i] = g
        worst = min(worst, best.fun)
        if best.fun < -1e-10:
            add(d, g); nadd += 1
    print(f'iter {it}: Q <= {Q:.9f} at ({x:.5f}, {y:.5f}, {b:.5f}); worst slack {worst:.2e}, added {nadd}', flush=True)
    if nadd == 0:
        break
Q, sol = solve_lp(win, states)
x, y, b = sol
print(f'CEILING {name} range {rng_s or "all"}: Q <= {Q:.9f} at ({x:.6f}, {y:.6f}, {b:.6f})')
binding = []
for (n1, n2, P, E), (lab, gaps) in zip(states, desc):
    if E - (x * n1 + y * n2 - b * P) < 1e-9:
        binding.append(dict(labels=lab, gaps=gaps, P=P, E=E))
        print('   binding:', lab, [round(v, 5) for v in gaps], 'P', round(P, 5), 'E', round(E, 7))
json.dump(dict(window=name, range=rng_s, maxsites=maxn, Q=Q, x=x, y=y, b=b, C=win.C, binding=binding), open(out, 'w'), indent=1)
