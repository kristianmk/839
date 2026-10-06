"""Tests of law_deep, the C++ program of the second stage of the search.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
of the author, who is responsible for its content.

1. Agreement with the Python reference (../law_lp.py) on the same problems: the cost reported for
   every configuration equals the cost recomputed in Python; every configuration is legal (marks 1
   or 2 with sum N, positions in order in [0, N), all gaps at least the minimum); every chain
   returns between one and keepCount configurations, and its best one is not worse than its start.
2. The result is reproducible: the output does not depend on the number of threads, and it
   depends on the seed.
3. Malformed and oversized input is rejected with the documented exit codes.
4. The same runs under AddressSanitizer and UndefinedBehaviorSanitizer (build_san/law_deep).

usage: law_deep_test.py            (needs build/law_deep and build_san/law_deep, see CMakeLists.txt)
"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np
import law_lp, law_cg
from law_oracle_test import problem

RELEASE = os.path.join(HERE, 'build', 'law_deep')
SANITIZE = os.path.join(HERE, 'build_san', 'law_deep')
SAN_ENV = dict(ASAN_OPTIONS='detect_leaks=1:abort_on_error=0', UBSAN_OPTIONS='halt_on_error=1:print_stacktrace=1')


def job_text(L, starts, steps=20, keep=4, temperature=1e-4, seed=1, iters=300):
    lines = [f'{L.N} {law_lp.GAP_MIN!r} {iters} {len(starts)} {steps} {keep} {temperature!r} {seed}',
             ' '.join(repr(float(v)) for v in L.y[:-1])]
    for x, d in starts:
        lines += [str(len(x)), ' '.join(repr(float(v)) for v in x), ' '.join(str(int(round(v))) for v in d)]
    return '\n'.join(lines) + '\n'


def run(binary, text, threads=1, extra_env=None):
    with tempfile.TemporaryDirectory() as td:
        fin, fout = os.path.join(td, 'in.txt'), os.path.join(td, 'out.txt')
        open(fin, 'w').write(text)
        env = dict(os.environ, OMP_NUM_THREADS=str(threads), **(extra_env or {}))
        r = subprocess.run([binary, fin, fout], env=env, capture_output=True, text=True)
        return r.returncode, r.stderr.strip(), (open(fout).read() if os.path.exists(fout) else None)


def parse(out, chains):
    """the configurations kept by each chain, as lists of (cost, x, d)"""
    lines = out.split('\n'); pos = 0; result = []
    for _ in range(chains):
        kept = []
        count = int(lines[pos]); pos += 1
        for _ in range(count):
            cost, n = lines[pos].split()
            x = np.array(lines[pos + 1].split(), float); d = np.array(lines[pos + 2].split(), float)
            assert int(n) == len(x) == len(d)
            kept.append((float(cost), x, d)); pos += 3
        result.append(kept)
    assert all(not line for line in lines[pos:])
    return result


def main():
    failures = 0
    def check(name, ok, detail=''):
        nonlocal failures
        failures += 0 if ok else 1
        print(f'{"ok  " if ok else "FAIL"} {name}{"  " + detail if detail else ""}', flush=True)

    # 1. agreement with the Python reference
    keep = 4
    for N, seed in ((16, 1), (32, 2), (64, 3)):
        L, cands = problem(N, seed, 24)
        starts = [law_cg.normalise(x, d, N) for x, d in cands]
        code, err, out = run(RELEASE, job_text(L, starts, keep=keep, seed=seed), threads=2)
        check(f'N = {N}: the run succeeds', code == 0 and out is not None, err[:120])
        if out is None:
            continue
        chains = parse(out, len(starts))
        flat = [c for kept in chains for c in kept]
        cpp = np.array([cost - L.y[-1] for cost, x, d in flat])
        own = np.array([L.reduced(x, d) for cost, x, d in flat])
        check(f'N = {N}: cost reported by law_deep equals the cost recomputed in Python', np.abs(cpp - own).max() < 1e-9,
              f'{len(flat)} configurations, max difference {np.abs(cpp - own).max():.1e}')
        marks_ok = all(set(np.unique(d)) <= {1.0, 2.0} and abs(d.sum() - N) < 1e-9 for _, x, d in flat)
        order_ok = all(x[0] >= 0 and x[-1] < N and np.all(np.diff(x) > 0) for _, x, d in flat)
        gap = min(np.diff(np.append(x, x[0] + N)).min() for _, x, d in flat)
        check(f'N = {N}: marks are 1 or 2 and sum to the period', marks_ok)
        check(f'N = {N}: positions in order, all gaps at least {law_lp.GAP_MIN}', order_ok and gap >= law_lp.GAP_MIN - 1e-9,
              f'smallest gap {gap:.6f}')
        check(f'N = {N}: every chain returns between 1 and {keep} configurations', all(1 <= len(k) <= keep for k in chains))
        legal = [i for i, (x, d) in enumerate(starts) if np.diff(np.append(x, x[0] + N)).min() >= law_lp.GAP_MIN + 1e-6]
        rise = max(min(c for c, _, _ in chains[i]) - L.y[-1] - L.reduced(*starts[i]) for i in legal)
        check(f'N = {N}: the best configuration of a chain is not worse than its start', rise <= 1e-9,
              f'{len(legal)} starts with legal gaps')
        changed = sum(1 for i, kept in enumerate(chains) if any(len(x) != len(starts[i][0]) for _, x, d in kept))
        check(f'N = {N}: some chains change the number of points', changed > 0, f'{changed} of {len(chains)} chains')

    # 2. reproducibility, and 4. sanitizers
    L, cands = problem(32, 5, 16); starts = [law_cg.normalise(x, d, L.N) for x, d in cands]
    text = job_text(L, starts, seed=7)
    outs = [run(RELEASE, text, threads=t) for t in (1, 2, 5)]
    check('the output does not depend on the number of threads', all(o[0] == 0 for o in outs) and outs[0][2] == outs[1][2] == outs[2][2])
    again = run(RELEASE, text, threads=3)
    check('the same job gives the same output again', again[2] == outs[0][2])
    other = run(RELEASE, job_text(L, starts, seed=8), threads=2)
    check('another seed gives another output', other[0] == 0 and other[2] != outs[0][2])
    code, err, out = run(SANITIZE, text, threads=3, extra_env=SAN_ENV)
    check('sanitizer build: valid job runs without a report', code == 0 and err == '' and out is not None, err[:200])
    code2, err2, out2 = run(SANITIZE, text, threads=1, extra_env=SAN_ENV)
    check('sanitizer build: the output does not depend on the number of threads', code2 == 0 and out2 == out and out is not None)
    # (the two builds are compiled with different optimisation, so their outputs are not compared with each other)

    # 3. malformed input, with both builds
    N = L.N; prices = ' '.join(repr(float(v)) for v in L.y[:-1]); tail = '20 4 1e-4 1'
    def cand(n, xs, ds):
        return f'{n}\n{xs}\n{ds}\n'
    ones = ' '.join(['1'] * N); grid = ' '.join(str(float(i)) for i in range(N))
    cases = {
        'empty file': ('', 3),
        'text instead of numbers': ('abc def\n', 3),
        'header without the four chain parameters': (f'{N} 0.5 10 0\n{prices}\n', 3),
        'period 1': (f'1 0.5 10 0 {tail}\n\n', 3),
        'negative period': (f'-4 0.5 10 0 {tail}\n1 1 1\n', 3),
        'period above the limit': (f'100000 0.5 10 0 {tail}\n', 3),
        'gap not positive': (f'{N} 0.0 10 0 {tail}\n{prices}\n', 3),
        'gap not a number': (f'{N} nan 10 0 {tail}\n{prices}\n', 3),
        'iteration limit 0': (f'{N} 0.5 0 0 {tail}\n{prices}\n', 3),
        'too many chains': (f'{N} 0.5 10 99999999 {tail}\n{prices}\n', 3),
        'too many steps': (f'{N} 0.5 10 0 99999999 4 1e-4 1\n{prices}\n', 3),
        'nothing to keep': (f'{N} 0.5 10 0 20 0 1e-4 1\n{prices}\n', 3),
        'too many to keep': (f'{N} 0.5 10 0 20 65 1e-4 1\n{prices}\n', 3),
        'negative temperature': (f'{N} 0.5 10 0 20 4 -1.0 1\n{prices}\n', 3),
        'temperature not a number': (f'{N} 0.5 10 0 20 4 nan 1\n{prices}\n', 3),
        'too few prices': (f'{N} 0.5 10 0 {tail}\n1.0 2.0\n', 3),
        'infinite price': (f'{N} 0.5 10 0 {tail}\n' + prices.replace(prices.split()[0], 'inf', 1) + '\n', 3),
        'chain missing': (f'{N} 0.5 10 1 {tail}\n{prices}\n', 3),
        'more points than the period': (f'{N} 0.5 10 1 {tail}\n{prices}\n' + cand(N + 1, grid + ' 0.5', ones + ' 1'), 3),
        'one point only': (f'{N} 0.5 10 1 {tail}\n{prices}\n' + cand(1, '0.0', str(N)), 3),
        'mark 3': (f'{N} 0.5 10 1 {tail}\n{prices}\n' + cand(N, grid, ones.replace('1', '3', 1)), 3),
        'mark 1.5': (f'{N} 0.5 10 1 {tail}\n{prices}\n' + cand(N, grid, ones.replace('1', '1.5', 1)), 3),
        'marks do not sum to the period': (f'{N} 0.5 10 1 {tail}\n{prices}\n' + cand(N - 1, ' '.join(grid.split()[:-1]), ' '.join(['1'] * (N - 1))), 3),
        'positions not sorted': (f'{N} 0.5 10 1 {tail}\n{prices}\n' + cand(N, ' '.join(reversed(grid.split())), ones), 3),
        'position outside the period': (f'{N} 0.5 10 1 {tail}\n{prices}\n' + cand(N, ' '.join(grid.split()[:-1]) + f' {float(N)}', ones), 3),
        'negative position': (f'{N} 0.5 10 1 {tail}\n{prices}\n' + cand(N, '-1.0 ' + ' '.join(grid.split()[1:]), ones), 3),
        'no room for the minimum gap': (f'{N} 1.0 10 1 {tail}\n{prices}\n' + cand(N, grid, ones), 3),
        'truncated positions': (f'{N} 0.5 10 1 {tail}\n{prices}\n{N}\n0.0 1.0\n', 3),
        'no chains (valid)': (f'{N} 0.5 10 0 {tail}\n{prices}\n', 0),
        'no steps (valid: the start is relaxed and returned)': (f'{N} 0.5 10 1 0 4 1e-4 1\n{prices}\n' + cand(N, grid, ones), 0),
        'temperature 0 (valid: only improvements are accepted)': (f'{N} 0.5 10 1 20 4 0.0 1\n{prices}\n' + cand(N, grid, ones), 0),
    }
    for name, (text, expected) in cases.items():
        for label, binary, env in (('release', RELEASE, None), ('sanitizer', SANITIZE, SAN_ENV)):
            code, err, out = run(binary, text, extra_env=env)
            clean = 'ERROR' not in err and 'runtime error' not in err
            check(f'{label}: {name} -> exit code {expected}', code == expected and clean and ((out is not None) == (expected == 0)),
                  f'got {code}: {err[:80]}' if code != expected or not clean else '')
    r = subprocess.run([RELEASE], capture_output=True, text=True)
    check('no arguments -> exit code 2', r.returncode == 2)
    r = subprocess.run([RELEASE, '/nonexistent/in.txt', '/nonexistent/out.txt'], capture_output=True, text=True)
    check('missing input file -> exit code 3', r.returncode == 3)
    with tempfile.TemporaryDirectory() as td:
        fin = os.path.join(td, 'in.txt'); open(fin, 'w').write(f'{N} 0.5 10 0 {tail}\n{prices}\n')
        r = subprocess.run([RELEASE, fin, '/nonexistent/dir/out.txt'], capture_output=True, text=True)
        check('output file cannot be written -> exit code 4', r.returncode == 4)

    print(f'\n{"ALL TESTS PASSED" if failures == 0 else str(failures) + " TESTS FAILED"}')
    sys.exit(0 if failures == 0 else 1)


if __name__ == '__main__':
    main()
