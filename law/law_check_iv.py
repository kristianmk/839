"""Second, independent check of a certified law (mpmath interval arithmetic; no FLINT).

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
of the author, who is responsible for its content.

Reads the exact data written by law_certify.py (rational positions and weights, integer marks) and
verifies again, with its own code:
  marks in {1, 2}; total multiplicity N in each configuration; points distinct and in [0, N);
  smallest gap; weights nonnegative with sum exactly 1;
  |N S(j) - j| <= tau for 0 < j < N, with S(j) = (1/N) sum_c w_c |sum_i d_i exp(2 pi i j x_i / N)|^2;
  the share of simple points p (exact rational).

usage: law_check_iv.py certified.json
"""
import sys, json
from fractions import Fraction as F
from mpmath import iv

iv.dps = 80


def ivq(q):
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def main():
    L = json.load(open(sys.argv[1])); N = L['N']; tau = F(L['tau'])
    law = [dict(w=F(c['w']), x=[F(v) for v in c['x']], d=c['d']) for c in L['law']]
    assert sum(c['w'] for c in law) == 1 and all(c['w'] >= 0 for c in law)
    mingap = None
    for c in law:
        assert all(d in (1, 2) for d in c['d']) and sum(c['d']) == N and len(c['d']) == len(c['x'])
        xs = c['x']; assert all(0 <= v < N for v in xs) and all(xs[i] < xs[i + 1] for i in range(len(xs) - 1))
        g = min([xs[i + 1] - xs[i] for i in range(len(xs) - 1)] + [xs[0] + N - xs[-1]])
        mingap = g if mingap is None else min(mingap, g)
    twopi = 2 * iv.pi
    worst = 0
    for j in range(1, N):
        tot = iv.mpf(0)
        for c in law:
            re = iv.mpf(0); im = iv.mpf(0)
            for x, d in zip(c['x'], c['d']):
                ang = twopi * ivq(F(j) * x / N)
                re += d * iv.cos(ang); im += d * iv.sin(ang)
            tot += ivq(c['w']) * (re * re + im * im)
        dev = tot - j
        hi = max(abs(dev.a), abs(dev.b))
        assert hi <= ivq(tau).a, (j, hi)
        worst = max(worst, float(hi))
    p = sum(c['w'] * c['d'].count(1) for c in law) / N
    assert p == F(L['p'])
    print(f'N = {N}: {len(law)} configurations, smallest gap {float(mingap):.6f}')
    print(f'CHECKED (mpmath intervals): |N S(j) - j| <= {worst:.2e} <= tau = {float(tau):.0e} for 0 < j < {N}')
    print(f'p = {float(p):.12f} (same rational as in the file), (1 + p)/2 = {float((1 + p) / 2):.12f}')


if __name__ == '__main__':
    main()
