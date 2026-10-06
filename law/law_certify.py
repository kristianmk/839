"""Certify a law of periodic marked configurations (exact rationals, ball arithmetic with python-flint).

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
of the author, who is responsible for its content.

Input: the floating-point law written by law_cg.py or law_lp.py.  The positions are rounded to rationals, the
weights are recomputed for the rounded configurations in high precision and rounded to rationals
that sum to 1, and then the following is checked rigorously:

  * each configuration has period N, marks in {1, 2}, total multiplicity N, and distinct points;
  * the weights are nonnegative rationals with sum 1;
  * the form factor  S(j) = (1/N) sum_c w_c |sum_i d_i exp(2 pi i j x_i / N)|^2  satisfies
    |N S(j) - j| <= tau  for 0 < j < N;
  * the mean share of simple points  p = sum_c w_c n_1(c) / N  (an exact rational).

usage: law_certify.py law.json out.json [digits of the positions, default 12]
"""
import sys, json
from fractions import Fraction as F
from flint import arb, acb, fmpq, ctx
import mpmath as mp

ctx.prec = 600
mp.mp.dps = 120
TAU = F(1, 10 ** 30)


def to_arb(q):
    return arb(fmpq(q.numerator, q.denominator))


def features(xs, ds, N):
    """arb enclosures of |sum d exp(2 pi i j x / N)|^2 for j = 1..N-1"""
    out = []
    for j in range(1, N):
        re = arb(0); im = arb(0)
        for x, d in zip(xs, ds):
            t = 2 * to_arb(F(j) * x / N)                     # angle / pi
            re += d * t.cos_pi(); im += d * t.sin_pi()
        out.append(re * re + im * im)
    return out


def main():
    L = json.load(open(sys.argv[1])); out = sys.argv[2]; D = int(sys.argv[3]) if len(sys.argv) > 3 else 12
    N = L['N']
    cols = []
    for c in L['law']:
        xs = sorted(F(round(v * 10 ** D), 10 ** D) % N for v in c['x'])
        order = sorted(range(len(c['x'])), key=lambda i: c['x'][i] % N)
        ds = [int(c['d'][i]) for i in order]
        assert all(d in (1, 2) for d in ds) and sum(ds) == N
        gaps = [xs[i + 1] - xs[i] for i in range(len(xs) - 1)] + [xs[0] + N - xs[-1]]
        assert min(gaps) > 0, 'points must be distinct'
        cols.append(dict(x=xs, d=ds, n1=ds.count(1), mingap=min(gaps), w0=c['w']))
    m = len(cols)
    print(f'N = {N}: {m} configurations, positions with {D} decimals, smallest gap {float(min(c["mingap"] for c in cols)):.4f}')
    feats = [features(c['x'], c['d'], N) for c in cols]
    # weights: solve the square system (N - 1 form factor rows and the row of ones) in high precision
    assert m == N, f'the support has {m} configurations, expected {N} (basic solution)'
    M = mp.matrix(N, N); b = mp.matrix(N, 1)
    for jj in range(N - 1):
        for k in range(N):
            M[jj, k] = mp.mpf(feats[k][jj].mid().str(100, radius=False))
        b[jj] = jj + 1
    for k in range(N):
        M[N - 1, k] = 1
    b[N - 1] = 1
    w = mp.lu_solve(M, b)
    wq = [F(int(mp.nint(v * 10 ** 60)), 10 ** 60) for v in w]
    k0 = max(range(N), key=lambda k: wq[k]); wq[k0] += 1 - sum(wq)
    assert sum(wq) == 1 and min(wq) >= 0, ('negative weight', float(min(wq)))
    print(f'weights: smallest {float(min(wq)):.3e}, largest {float(max(wq)):.4f}; change against the search at most {max(abs(float(a) - c["w0"]) for a, c in zip(wq, cols)):.2e}')
    worst = arb(0)
    for jj in range(N - 1):
        tot = arb(0)
        for k in range(N):
            tot += to_arb(wq[k]) * feats[k][jj]
        dev = abs(tot - (jj + 1))
        assert dev < to_arb(TAU), (jj + 1, dev.str(10))
        worst = worst.max(dev) if hasattr(worst, 'max') else dev
    p = sum(wq[k] * cols[k]['n1'] for k in range(N)) / N
    tau0 = F(1, 6 * N * N) + TAU / (2 * N)
    ceil10 = (1 + p) / 2 + (1 - p) * 10 * tau0 / (1 + 20 * tau0)
    print(f'CERTIFIED: |N S(j) - j| <= {float(TAU):.0e} for 0 < j < {N}; weights sum to 1; points distinct')
    print(f'share of simple points p = {float(p):.10f}   (1 + p)/2 = {float((1 + p) / 2):.10f}')
    print(f'tau0 = 1/(6 N^2) + tau/(2N) = {float(tau0):.6e}; ceiling for V <= 10 B: {float(ceil10):.8f}')
    json.dump(dict(N=N, tau=str(TAU), p=str(p), p_float=float(p), ceiling_V_le_10B=float(ceil10),
                   law=[dict(w=str(wq[k]), x=[str(v) for v in cols[k]['x']], d=cols[k]['d']) for k in range(N)]),
              open(out, 'w'), indent=0)


if __name__ == '__main__':
    main()
