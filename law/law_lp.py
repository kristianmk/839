"""A law of periodic marked configurations with the pair correlation of the zeros in the band:
statement of the problem, and a reference implementation of the search in pure Python.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
of the author, who is responsible for its content.

The production search is law_cg.py (same problem, linear programme kept in HiGHS, local
optimisation in C++). This file is kept as the reference: law_oracle_test.py checks the C++ kernel
against the optimiser here, and for small periods the search here can be run on its own. The
result of either search is a floating-point law; it is certified separately (law_certify.py).

Configurations: period N, points 0 <= x_1 < ... < x_n < N with marks d_i in {1, 2}, sum d_i = N.
Form factor of a configuration:  v_j = |sum_i d_i exp(2 pi i j x_i / N)|^2,  j = 1..N-1.
A law (weights w_c >= 0, sum 1) is admissible if  sum_c w_c v_{c,j} = j  for 0 < j < N, the values
for Haar unitary matrices of size N (E |tr U^j|^2 = j).  We minimise the mean share of simple
points  p = sum_c w_c n_1(c) / N  by linear programming with column generation: for dual prices
y_j the best new configuration minimises  n_1/N - sum_j y_j v_j, a ground-state problem for the
pair potential  -sum_j y_j cos(2 pi j t / N).

usage: law_lp.py N rounds out.json [seed [law_of_half_the_period.json]]
"""
import sys, json, time, os
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')   # the matrices here are small: threads of the linear algebra library only slow it down
import numpy as np
from scipy.optimize import linprog, minimize


def features(x, d, N):
    j = np.arange(1, N)
    z = (d[None, :] * np.exp(2j * np.pi * np.outer(j, x) / N)).sum(axis=1)
    return (z.real ** 2 + z.imag ** 2)


def haar_positions(N, rs):
    z = (rs.normal(size=(N, N)) + 1j * rs.normal(size=(N, N))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    q = q * (np.diag(r) / np.abs(np.diag(r)))
    return np.sort(np.mod(np.angle(np.linalg.eigvals(q)), 2 * np.pi) * N / (2 * np.pi))


def lattice_config(N, k, rs, jitter=0.0):
    """N - 2k simple and k double points: sites of a lattice with spacing N/n, doubles at random sites"""
    n = N - k
    d = np.ones(n); d[rs.choice(n, size=k, replace=False)] = 2
    # put the points so that the multiplicity is spread evenly: position = centre of mass of its units
    c = np.cumsum(d); x = c - d / 2
    x = np.mod(x + rs.uniform(0, N) + jitter * rs.normal(size=n), N)
    o = np.argsort(x)
    return x[o], d[o]


class Law:
    def __init__(self, N, seed=0):
        self.N = N; self.rs = np.random.default_rng(seed); self.cols = []
    def add(self, x, d):
        x = np.mod(np.asarray(x, float), self.N); o = np.argsort(x); x = x[o]; d = np.asarray(d, float)[o]
        assert abs(d.sum() - self.N) < 1e-9
        self.cols.append(dict(x=x, d=d, v=features(x, d, self.N), n1=float((d == 1).sum())))
    def solve(self):
        N = self.N
        V = np.array([c['v'] for c in self.cols]).T                # (N-1, ncols)
        A = np.vstack([V, np.ones(V.shape[1])]); b = np.append(np.arange(1, N), 1.0)
        cost = np.array([c['n1'] for c in self.cols]) / N
        res = linprog(cost, A_eq=A, b_eq=b, bounds=(0, None), method='highs')
        if res.status != 0:
            return None
        self.w = res.x; self.y = res.eqlin.marginals; self.p = res.fun
        return res.fun
    def reduced(self, x, d):
        return float((d == 1).sum()) / self.N - self.y[:-1] @ features(np.mod(x, self.N), d, self.N) - self.y[-1]
    def improve(self, x, d, iters=200):
        """local minimum of the reduced cost over the positions, with all gaps at least GAP_MIN:
        gaps = GAP_MIN + (N - n GAP_MIN) softmax(u), first point at 0 (the features do not depend on a shift)"""
        N = self.N; y = self.y[:-1]; j = np.arange(1, N); n = len(x)
        x = np.sort(np.mod(x, N)); g = np.diff(np.append(x, x[0] + N))
        S = N - n * GAP_MIN
        u0 = np.log(np.maximum(g - GAP_MIN, 1e-6) / S)
        def fg(u):
            e = np.exp(u - u.max()); sm = e / e.sum()
            gaps = GAP_MIN + S * sm
            pos = np.concatenate(([0.0], np.cumsum(gaps[:-1])))
            ph = np.exp(2j * np.pi * np.outer(j, pos) / N)
            z = ph @ d
            val = -(y * (z.real ** 2 + z.imag ** 2)).sum()
            gx = -(2 * np.real(np.conj(z)[:, None] * ph * (2j * np.pi * j[:, None] / N)) * y[:, None]).sum(axis=0) * d
            a = np.zeros(n); a[:-1] = np.cumsum(gx[::-1])[::-1][1:]          # dG/dgap_k = sum_{i>k} dG/dx_i
            gu = S * (sm * a - sm * (sm @ a))
            return val, gu
        r = minimize(fg, u0, jac=True, method='L-BFGS-B', options=dict(maxiter=iters))
        e = np.exp(r.x - r.x.max()); gaps = GAP_MIN + S * e / e.sum()
        return np.concatenate(([0.0], np.cumsum(gaps[:-1])))


GAP_MIN = 0.5


def dump(L, out):
    supp = [(float(w), c) for c, w in zip(L.cols, L.w) if w > 1e-12]
    json.dump(dict(N=L.N, p=float(L.p), law=[dict(w=w, x=c['x'].tolist(), d=c['d'].astype(int).tolist()) for w, c in supp]), open(out, 'w'))
    return supp


def settle(L, x, d):
    x = np.sort(np.mod(x, L.N))
    return L.improve(x, d), d


def run(N, rounds, out, seed=0, log=print, warm=None):
    L = Law(N, seed); rs = L.rs; t0 = time.time()
    for _ in range(4 * N):
        L.add(haar_positions(N, rs), np.ones(N))
    for k in range(0, N // 2 + 1):
        for _ in range(6):
            L.add(*lattice_config(N, k, rs, jitter=0.0)); L.add(*lattice_config(N, k, rs, jitter=0.15))
    if warm:                                                        # columns made of configurations of a shorter period
        W = json.load(open(warm)); M = W['N']; parts = N // M; assert parts * M == N and parts >= 2
        ws = np.array([c['w'] for c in W['law']]); ws = ws / ws.sum()
        for _ in range(6 * N):
            xs = []; ds = []
            for q, a in enumerate(rs.choice(len(ws), size=parts, p=ws)):
                c = W['law'][a]; sh = rs.uniform(0, M); xx = np.mod(np.array(c['x']) + sh, M); o = np.argsort(xx)
                xs.append(q * M + xx[o]); ds.append(np.array(c['d'])[o])
            L.add(np.concatenate(xs), np.concatenate(ds))
    p = L.solve(); log(f'N = {N}: start with {len(L.cols)} columns, p = {p}')
    for it in range(rounds):
        added = 0; best = 0.0
        supp = [c for c, w in zip(L.cols, L.w) if w > 1e-9]
        cands = []
        for c in supp:                                              # perturb and mutate the support
            cands.append((c['x'] + rs.normal(0, 0.05, len(c['x'])), c['d']))
            x, d = c['x'].copy(), c['d'].copy()
            if rs.random() < 0.5 and (d == 1).sum() >= 2:           # merge two neighbouring simple points
                i = rs.integers(len(x) - 1)
                if d[i] == 1 and d[i + 1] == 1:
                    x[i] = 0.5 * (x[i] + x[i + 1]); d[i] = 2; x = np.delete(x, i + 1); d = np.delete(d, i + 1)
            elif (d == 2).any():                                    # split a double point
                i = rs.choice(np.nonzero(d == 2)[0])
                x = np.insert(x, i + 1, x[i] + 0.5); d[i] = 1; d = np.insert(d, i + 1, 1); x[i] -= 0.5
            cands.append((x, d))
        for k in rs.integers(0, N // 2 + 1, size=12):
            cands.append(lattice_config(N, int(k), rs, jitter=0.2))
        for x, d in cands:
            x2, d2 = settle(L, np.asarray(x, float), np.asarray(d, float))
            if x2 is None:
                continue
            rc = L.reduced(x2, d2)
            best = min(best, rc)
            if rc < -1e-9:
                L.add(x2, d2); added += 1
        p = L.solve()
        log(f'round {it}: p = {p:.6f}   ceiling (1+p)/2 = {(1 + p) / 2:.6f}   added {added}, best reduced cost {best:.2e}, columns {len(L.cols)}  [{time.time() - t0:.0f} s]')
        if it % 25 == 24:
            dump(L, out)
        if added == 0:
            break
    supp = dump(L, out)
    log(f'support: {len(supp)} configurations; double points per period (weighted): {sum(w * (c["d"] == 2).sum() for w, c in supp):.3f}')


if __name__ == '__main__':
    N = int(sys.argv[1]); rounds = int(sys.argv[2]); out = sys.argv[3]; seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    warm = sys.argv[5] if len(sys.argv) > 5 else None
    run(N, rounds, out, seed, log=lambda s: print(s, flush=True), warm=warm)
