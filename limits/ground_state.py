# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
"""Variational ceilings for the labelled Gram method (floating point, not a proof).

For a window f on [-1/2, 1/2] with kernel K = f^ and autocorrelation R = f*f (so K^2 = R^),
a certificate of the method is a triple (x, y, b) with

    F(Y, D) := sum_{i != j} d_i d_j K(y_i - y_j)^2  >=  x n_1 + y n_2 - b span - O(1)

for all labelled configurations, and it proves
    Q(x, y, b) = (3 - C + y - x - b) / (2 - 2x + y).

Every periodic configuration (period length P, points y_i with labels d_i) gives the linear
constraint  x n_1 + y n_2 - b P <= E_pair(per period).  The exact period energy is, by Poisson
summation (R is supported in [-1, 1], so the sum is finite),

    E_pair = (1/P) sum_{|m| <= P} R(m/P) |sum_i d_i e(m y_i / P)|^2 - sum_i d_i^2 .

Maximising Q under the constraints of a family of trial states gives an upper bound for what
any certificate can prove with this window ("ceiling").  Trial states are refined by a cutting
plane loop: solve the LP, then minimise the slack of each label pattern over its gaps.

Range-s variant: only pairs at index distance <= s are counted (what a window of s+1 points sees).

usage: ground_state.py [window] [maxperiod] [range]
  window: new | mt | paper1 | flat      range: 0 = all pairs, else s
"""
import sys, itertools
import numpy as np
from scipy.optimize import linprog, minimize

A_NEW = np.array([193305, -23105, 29166, 13952, -21009, 41052]) / 1e6
KAPPA1 = np.array([3322500, -7609135, 1190194, -731476, -1680572, 1141360]) * 1e-9


def window(name):
    """return (freqs, coefs) with f(u) proportional to sum c_k cos(w_k u) on [-1/2, 1/2]"""
    if name == 'new':
        w = np.concatenate(([0.0], 2 * np.pi * np.arange(1, 7)))
        c = np.concatenate(([1.0], A_NEW))
    elif name == 'mt':
        w = np.array([np.sqrt(2.0)]); c = np.array([1.0])
    elif name == 'paper1':
        w = np.concatenate(([np.sqrt(2.0)], 2 * np.pi * np.arange(1, 7)))
        c = np.concatenate(([1.0], KAPPA1))
    elif name == 'flat':
        w = np.array([0.0]); c = np.array([1.0])
    else:
        raise SystemExit('unknown window')
    # normalise: int f = 1
    integ = sum(ck * (1.0 if wk == 0 else 2 * np.sin(wk / 2) / wk) for wk, ck in zip(w, c))
    return w, c / integ


class Win:
    def __init__(self, name):
        self.w, self.c = window(name)
        self.gx, self.gw = np.polynomial.legendre.leggauss(400)
        u = np.linspace(0, 1, 20001)
        self.Rtab_u = u
        self.Rtab = np.array([self.R(t) for t in u])
        # C(f) = R(0) + 2 int_0^1 u R(u) du  (Gauss-Legendre on [0,1])
        uu = 0.5 * (self.gx + 1); ww = 0.5 * self.gw
        self.C = self.R(0.0) + 2 * np.sum(ww * uu * np.array([self.R(t) for t in uu]))

    def f(self, u):
        return sum(ck * np.cos(wk * u) for wk, ck in zip(self.w, self.c))

    def R(self, u):
        u = abs(u)
        if u >= 1:
            return 0.0
        lo, hi = u - 0.5, 0.5
        t = 0.5 * (hi - lo) * self.gx + 0.5 * (hi + lo)
        return 0.5 * (hi - lo) * np.sum(self.gw * self.f(t) * self.f(u - t))

    def K(self, t):
        t = np.asarray(t, dtype=float)
        out = np.zeros_like(t)
        for wk, ck in zip(self.w, self.c):
            for sgn in (1, -1):
                z = (wk + sgn * 2 * np.pi * t) / 2
                out += 0.5 * ck * np.sinc(z / np.pi)
        return out


def energy_full(win, gaps, labs):
    """exact pair energy per period, all pairs"""
    gaps = np.asarray(gaps, float); d = np.asarray(labs, float)
    P = gaps.sum(); y = np.concatenate(([0.0], np.cumsum(gaps)[:-1]))
    M = int(np.floor(P))
    tot = win.R(0.0) * d.sum() ** 2
    for m in range(1, M + 1):
        S = np.sum(d * np.exp(2j * np.pi * m * y / P))
        tot += 2 * win.R(m / P) * abs(S) ** 2
    return tot / P - np.sum(d * d)


def energy_range(win, gaps, labs, s):
    """pair energy per period counting only pairs at index distance <= s"""
    gaps = np.asarray(gaps, float); d = np.asarray(labs, float); p = len(d)
    tot = 0.0
    for i in range(p):
        dist = 0.0
        for r in range(1, s + 1):
            dist += gaps[(i + r - 1) % p]
            tot += 2 * d[i] * d[(i + r) % p] * win.K(dist) ** 2
    return float(tot)


def patterns(maxp):
    seen = set(); out = []
    for p in range(1, maxp + 1):
        for lab in itertools.product((1, 2), repeat=p):
            # primitive, canonical under rotation and reflection
            rots = [lab[i:] + lab[:i] for i in range(p)]
            rots += [tuple(reversed(r)) for r in rots]
            can = min(rots)
            if can in seen:
                continue
            if any(p % q == 0 and lab == lab[:q] * (p // q) for q in range(1, p)):
                continue
            seen.add(can); out.append(can)
    return out


def solve_lp(win, states):
    """maximise Q over (x, y, b) >= 0, x <= y, subject to the trial states (bisection on Q)"""
    A = []; rhs = []
    for (n1, n2, P, E) in states:
        A.append([n1, n2, -P]); rhs.append(E)
    A.append([1, -1, 0]); rhs.append(0.0)          # x <= y
    A = np.array(A); rhs = np.array(rhs)
    lo, hi = (3 - win.C) / 2 - 1e-9, 0.95
    best = None
    for _ in range(60):
        Q = 0.5 * (lo + hi)
        # feasibility: (2Q-1) x + (1-Q) y - b >= 2Q - 3 + C ; maximise the left side
        res = linprog(c=[-(2 * Q - 1), -(1 - Q), 1.0], A_ub=A, b_ub=rhs,
                      bounds=[(0, 1), (0, 1), (0, 1)], method='highs')
        if res.status == 0 and -res.fun >= 2 * Q - 3 + win.C - 1e-13:
            lo = Q; best = res.x
        else:
            hi = Q
    return lo, best


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else 'new'
    maxp = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    rng = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    win = Win(name)
    en = (lambda g, l: energy_full(win, g, l)) if rng == 0 else (lambda g, l: energy_range(win, g, l, rng))
    print(f'window {name}: C = {win.C:.12f}, baseline (3-C)/2 = {(3 - win.C) / 2:.6f}, '
          f'range = {"all" if rng == 0 else rng}, patterns up to period {maxp}', flush=True)
    pats = patterns(maxp)
    states = []; desc = []
    def add(lab, gaps):
        n1 = sum(1 for a in lab if a == 1); n2 = len(lab) - n1
        states.append((n1, n2, float(np.sum(gaps)), en(gaps, lab)))
        desc.append((lab, tuple(np.round(gaps, 5))))
    for lab in pats:
        for s in np.arange(0.7, 3.01, 0.05):
            add(lab, [s] * len(lab))
    rngen = np.random.default_rng(1)
    for it in range(40):
        Q, sol = solve_lp(win, states)
        x, y, b = sol
        worst = 0.0; nadd = 0
        for lab in pats:
            p = len(lab); n1 = sum(1 for a in lab if a == 1); n2 = p - n1
            def slack(g):
                g = np.abs(g) + 1e-3
                return en(g, lab) - (x * n1 + y * n2 - b * g.sum())
            best = None
            starts = [np.full(p, s) for s in (0.9, 1.0, 1.1, 1.5, 2.0)]
            starts += [rngen.uniform(0.6, 2.4, size=p) for _ in range(6)]
            for g0 in starts:
                r = minimize(slack, g0, method='Nelder-Mead',
                             options=dict(xatol=1e-7, fatol=1e-12, maxiter=4000))
                if best is None or r.fun < best.fun:
                    best = r
            if best.fun < -1e-9:
                add(lab, np.abs(best.x) + 1e-3); nadd += 1
            worst = min(worst, best.fun)
        print(f'iter {it}: Q <= {Q:.6f} at (x, y, b) = ({x:.5f}, {y:.5f}, {b:.5f}); '
              f'worst slack {worst:.2e}, added {nadd}', flush=True)
        if nadd == 0:
            break
    Q, sol = solve_lp(win, states)
    x, y, b = sol
    print(f'CEILING {name} range {"all" if rng == 0 else rng}: Q <= {Q:.6f} at (x, y, b) = ({x:.6f}, {y:.6f}, {b:.6f})')
    # binding states
    print('binding trial states (slack < 1e-7):')
    for (n1, n2, P, E), (lab, gaps) in zip(states, desc):
        if E - (x * n1 + y * n2 - b * P) < 1e-7:
            print('   labels', lab, 'gaps', gaps, 'energy/period', round(E, 6))


if __name__ == '__main__':
    main()
