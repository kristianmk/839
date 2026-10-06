# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
"""Certified ceilings for the critical-line problem (ball arithmetic, python-flint).

Window of Theorem 3 (`line` in ceiling_certified.py).  Only simple points interact.  A pair (x, b),
b >= 0, x < 1, is a certificate of range s if, for some constant and all sets Y of n points with gaps
at least 17/20,
        sum over pairs at index distance <= s (or over all pairs) of K(y_i - y_j)^2
            >=  x n - b span(Y) - const,
and it then gives the constant (2 - C(f) - b)/(1 - x).  Apply this to M periods of a periodic state
with n_k points, period P_k and pair energy e_k per period, divide by M and let M -> infinity:
x n_k - b P_k <= e_k.  For weights w_k >= 0 with

        sum_k w_k (e_k - n_k + (2 - C(f)) P_k)  <=  0

the weighted sum gives  (2 - C - b)/(1 - x)  <=  sum_k w_k n_k / sum_k w_k P_k.

This script encloses e_k (Poisson summation for all pairs, integer periods; finite sums of values of
K^2 for a finite range), chooses rational weights and checks the displayed inequality.

usage: ceiling_line_certified.py states.json [range]
"""
import sys, json
from fractions import Fraction
from scipy.optimize import linprog
from flint import arb
from ceiling_certified import Win, to_arb


def main():
    data = json.load(open(sys.argv[1])); rng = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    win = Win('line')
    print('window line  C(f) =', win.C.str(20), '  2 - C(f) =', (2 - win.C).str(20))
    states = []
    for st in data['binding']:
        g = [Fraction(v) for v in st['gaps']]
        assert all(d == 1 for d in st['labels']) and min(g) >= Fraction(17, 20)
        n = len(g); P = sum(g)
        if rng == 0:
            assert P.denominator == 1
            E = win.period_energy([1] * n, g)
        else:
            E = win.period_energy_range([1] * n, g, rng)
        e = E - n
        states.append(dict(gaps=g, n=n, P=P, e=e))
        print('  state gaps', [str(x) for x in g], ' n', n, ' P', P, ' pair energy e =', e.str(15))
    twoC = float((2 - win.C).mid()); margin = 1e-10
    res = linprog(c=[s['n'] for s in states],
                  A_ub=[[float(s['e'].mid()) - s['n'] + twoC * float(s['P']) for s in states]], b_ub=[-margin],
                  A_eq=[[float(s['P']) for s in states]], b_eq=[1.0], bounds=[(0, None)] * len(states), method='highs')
    assert res.status == 0
    w = [Fraction(max(v, 0.0)).limit_denominator(10 ** 9) for v in res.x]
    nt = sum(wk * s['n'] for wk, s in zip(w, states)); Pt = sum(wk * s['P'] for wk, s in zip(w, states))
    lhs = sum((to_arb(wk) * (s['e'] - s['n'] + (2 - win.C) * to_arb(s['P'])) for wk, s in zip(w, states)), arb(0))
    ok = bool(lhs < 0)
    Q = nt / Pt
    print('weights', [str(x) for x in w])
    print('sum w (e - n + (2 - C) P) =', lhs.str(10), '  negative (certified):', ok)
    tag = 'all pairs' if rng == 0 else f'range {rng}'
    print(f'CERTIFIED CEILING line, {tag}: (2 - C - b)/(1 - x) <= {Q} = {float(Q):.9f}' if ok else 'NOT CERTIFIED')


if __name__ == '__main__':
    main()
