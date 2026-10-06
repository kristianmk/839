"""Search for a law of periodic marked configurations by column generation.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
of the author, who is responsible for its content.

The problem is stated in law_lp.py, which also holds a slower reference implementation in pure
Python. Here the restricted linear programme is kept in HiGHS and solved again from the previous
basis after new columns are added, and the local optimisation of the candidates is done by the
C++ program law_oracle (law_oracle.cpp), which runs the candidates in parallel.

The output is a floating-point law. It carries no proof obligation: law_certify.py turns it into
exact rational data and verifies the properties that are used, and law_check_iv.py verifies them
again with independent code.

usage: law_cg.py N rounds out.json [seed [law_of_a_shorter_period.json or - [threads]]]
"""
import sys, json, os, time, subprocess, tempfile
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')   # the matrices here are small: threads of the linear algebra library only slow it down
import numpy as np
import highspy
from law_lp import features, haar_positions, lattice_config, GAP_MIN

HERE = os.path.dirname(os.path.abspath(__file__))
BINARY = os.path.join(HERE, 'build', 'law_oracle')
ACCEPT = -1e-9                      # a candidate is added if its reduced cost is below this
STALL_ROUNDS = 150                  # stop if p has decreased by less than STALL_GAIN in so many rounds
STALL_GAIN = 2e-9


def normalise(x, d, N):
    """positions in [0, N) in increasing order, with the marks in the same order"""
    x = np.mod(np.asarray(x, float), N)
    x[x >= N] = 0.0                                          # np.mod can return N for tiny negative input
    o = np.argsort(x, kind='stable')
    return x[o], np.asarray(d, float)[o]


def write_job(path, N, prices, cands, iters):
    """the input file of law_oracle; the candidates must be normalised"""
    with open(path, 'w') as fh:
        fh.write(f'{N} {GAP_MIN!r} {iters} {len(cands)}\n' + ' '.join(repr(float(v)) for v in prices) + '\n')
        for x, d in cands:
            fh.write(f'{len(x)}\n' + ' '.join(repr(float(v)) for v in x) + '\n' + ' '.join(str(int(round(v))) for v in d) + '\n')


def read_results(path, cands):
    out = []
    with open(path) as fh:
        for x, d in cands:
            val, n = fh.readline().split(); xs = np.array(fh.readline().split(), float)
            assert int(n) == len(x) == len(xs)
            out.append((float(val), xs, d))
    return out


def oracle(L, cands, threads, iters=300, binary=None):
    """local minima of the reduced cost from the given starts, computed by law_oracle;
    L supplies the period L.N and the prices L.y (the last entry belongs to the row sum w = 1)"""
    cands = [normalise(x, d, L.N) for x, d in cands]
    with tempfile.TemporaryDirectory() as td:
        fin, fout = os.path.join(td, 'in.txt'), os.path.join(td, 'out.txt')
        write_job(fin, L.N, L.y[:-1], cands, iters)
        env = dict(os.environ, OMP_NUM_THREADS=str(threads))
        subprocess.run([binary or BINARY, fin, fout], check=True, env=env)
        return read_results(fout, cands)


class RestrictedProgramme:
    """The linear programme restricted to the configurations found so far:
    minimise sum_c w_c n_1(c) / N  subject to  sum_c w_c v_{c,j} = j (0 < j < N), sum_c w_c = 1, w >= 0."""

    def __init__(self, N):
        self.N = N; self.cols = []
        h = highspy.Highs()
        h.setOptionValue('output_flag', False)
        h.setOptionValue('presolve', 'off')
        h.setOptionValue('solver', 'simplex')
        h.setOptionValue('simplex_strategy', 4)              # primal simplex: the old basis stays feasible when columns are added
        h.setOptionValue('threads', 1)
        h.setOptionValue('primal_feasibility_tolerance', 1e-9)
        h.setOptionValue('dual_feasibility_tolerance', 1e-9)
        for j in range(1, N):
            h.addRow(float(j), float(j), 0, [], [])
        h.addRow(1.0, 1.0, 0, [], [])
        self.h = h; self.rows = np.arange(N, dtype=np.int32)

    def add(self, x, d, v=None):
        x, d = normalise(x, d, self.N)
        assert abs(d.sum() - self.N) < 1e-9
        v = features(x, d, self.N) if v is None else v
        n1 = float((d == 1).sum())
        self.h.addCol(n1 / self.N, 0.0, highspy.kHighsInf, self.N, self.rows, np.append(v, 1.0))
        self.cols.append(dict(x=x, d=d, n1=n1))

    def solve(self):
        self.h.run()
        status = self.h.getModelStatus()
        if status != highspy.HighsModelStatus.kOptimal:      # solve once more, without the old basis
            self.h.clearSolver(); self.h.run(); status = self.h.getModelStatus()
        assert status == highspy.HighsModelStatus.kOptimal, f'linear programme not solved: {status}'
        sol = self.h.getSolution()
        self.w = np.array(sol.col_value); self.y = np.array(sol.row_dual); self.rc = np.array(sol.col_dual)
        self.basic = np.array([s == highspy.HighsBasisStatus.kBasic for s in self.h.getBasis().col_status])
        self.p = float(self.h.getInfo().objective_function_value)
        return self.p

    def reduced(self, v, n1):
        return n1 / self.N - self.y[:-1] @ v - self.y[-1]

    def prune(self, limit, keep):
        """if there are more than `limit` columns, delete nonbasic ones with the largest reduced cost until `keep` remain"""
        if len(self.cols) <= limit:
            return
        m = len(self.w)                                      # columns that were in the last solve
        order = [i for i in np.argsort(-self.rc[:m]) if not self.basic[i]]
        drop = np.array(sorted(order[:len(self.cols) - keep]), dtype=np.int32)
        if len(drop):
            self.h.deleteCols(len(drop), drop)
            gone = set(drop.tolist()); self.cols = [c for i, c in enumerate(self.cols) if i not in gone]


def dump(lp, out, meta):
    """write the basic columns of the last solve (a basis has N of them unless it is degenerate)"""
    law = [dict(w=float(lp.w[i]), x=lp.cols[i]['x'].tolist(), d=lp.cols[i]['d'].astype(int).tolist()) for i in np.nonzero(lp.basic)[0]]
    with open(out + '.tmp', 'w') as fh:
        json.dump(dict(N=lp.N, p=lp.p, minimum_gap=GAP_MIN, **meta, law=law), fh)
    os.replace(out + '.tmp', out)
    return law


def mutate(c, rs, N):
    """a neighbour of a configuration: merge two simple points, split a double point, or move a double point"""
    x, d = c['x'].copy(), c['d'].copy(); n = len(x); r = rs.random()
    if r < 0.35:                                             # merge two neighbouring simple points
        idx = [i for i in range(n - 1) if d[i] == 1 and d[i + 1] == 1]
        if idx:
            i = int(rs.choice(idx)); x[i] = 0.5 * (x[i] + x[i + 1]); d[i] = 2; x = np.delete(x, i + 1); d = np.delete(d, i + 1)
    elif r < 0.7:                                            # split a double point
        idx = np.nonzero(d == 2)[0]
        if len(idx):
            i = int(rs.choice(idx)); x = np.insert(x, i + 1, x[i] + 0.5); d[i] = 1; d = np.insert(d, i + 1, 1); x[i] -= 0.5
    else:                                                    # move a double point to a neighbouring site
        idx = [i for i in range(n - 1) if d[i] != d[i + 1]]
        if idx:
            i = int(rs.choice(idx)); d[i], d[i + 1] = d[i + 1], d[i]
    return x, d


def run(N, rounds, out, seed=0, warm=None, threads=9, log=print):
    rs = np.random.default_rng(seed); lp = RestrictedProgramme(N); t0 = time.time()
    meta = dict(program='law_cg.py', seed=seed, warm_start=os.path.basename(warm) if warm else None)
    for _ in range(3 * N):                                   # eigenvalue angles of Haar unitary matrices
        lp.add(haar_positions(N, rs), np.ones(N))
    for k in range(0, N // 2 + 1, max(1, N // 64)):          # lattices with k double points
        for _ in range(4):
            lp.add(*lattice_config(N, k, rs, jitter=0.0)); lp.add(*lattice_config(N, k, rs, jitter=0.15))
    if warm:                                                 # configurations of a shorter period, placed one after the other
        W = json.load(open(warm)); P = W['N']; parts = N // P; assert parts * P == N
        ws = np.array([c['w'] for c in W['law']]); ws = np.maximum(ws, 0); ws = ws / ws.sum()
        for c in (W['law'] if parts == 1 else []):           # same period: continue from that law
            lp.add(np.array(c['x']), np.array(c['d'], float))
        for _ in range(6 * N if parts > 1 else 0):
            xs = []; ds = []
            for q, a in enumerate(rs.choice(len(ws), size=parts, p=ws)):
                c = W['law'][a]; xx, dd = normalise(np.array(c['x']) + rs.uniform(0, P), np.array(c['d'], float), P)
                xs.append(q * P + xx); ds.append(dd)
            lp.add(np.concatenate(xs), np.concatenate(ds))
    p = lp.solve(); history = [p]
    log(f'N = {N}: start with {len(lp.cols)} columns, p = {p:.8f}  [{time.time() - t0:.0f} s]')
    for it in range(rounds):
        supp = [c for c, w in zip(lp.cols, lp.w) if w > 1e-9]
        cands = []
        for c in supp:                                       # perturb and mutate the support
            cands.append((c['x'] + rs.normal(0, 0.05, len(c['x'])), c['d']))
            cands.append(mutate(c, rs, N))
            cands.append(mutate(c, rs, N))
        for k in rs.integers(0, N // 2 + 1, size=16):
            cands.append(lattice_config(N, int(k), rs, jitter=0.2))
        t1 = time.time(); res = oracle(lp, cands, threads); t_kernel = time.time() - t1
        added = 0; best = 0.0; seen = set()
        for _, x, d in res:
            v = features(x, d, N); n1 = float((d == 1).sum()); rc = lp.reduced(v, n1)   # recomputed here, not taken from the kernel
            best = min(best, rc); key = (len(x), round(rc, 9))
            if rc < ACCEPT and key not in seen:              # equal keys: the same local minimum reached twice
                seen.add(key); lp.add(x, d, v); added += 1
        lp.prune(limit=10 * N, keep=6 * N)
        t1 = time.time(); p = lp.solve(); t_lp = time.time() - t1; history.append(p)
        log(f'round {it}: p = {p:.9f}  (1+p)/2 = {(1 + p) / 2:.9f}  added {added}, best reduced cost {best:.2e}, columns {len(lp.cols)}'
            f'  [kernel {t_kernel:.1f} s, LP {t_lp:.1f} s, total {time.time() - t0:.0f} s]')
        if it % 20 == 19:
            dump(lp, out, dict(meta, rounds=it + 1, finished=False))
        if added == 0 or (len(history) > STALL_ROUNDS and history[-1 - STALL_ROUNDS] - p < STALL_GAIN):
            break
    law = dump(lp, out, dict(meta, rounds=len(history) - 1, finished=True))
    doubles = sum(c['w'] * c['d'].count(2) for c in law)
    log(f'finished: p = {lp.p:.10f}, {len(law)} basic configurations, double points per period (weighted) {doubles:.3f}')


if __name__ == '__main__':
    N = int(sys.argv[1]); rounds = int(sys.argv[2]); out = sys.argv[3]
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    warm = sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != '-' else None
    threads = int(sys.argv[6]) if len(sys.argv) > 6 else 9
    run(N, rounds, out, seed, warm, threads, log=lambda s: print(s, flush=True))
