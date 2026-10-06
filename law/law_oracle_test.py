"""Tests of law_oracle, the C++ kernel of the search.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
of the author, who is responsible for its content.

1. Agreement with the Python reference (law_lp.py) on the same problems: the value reported by the
   kernel equals the value recomputed in Python; the results respect the minimum gap, are not
   worse than the start, and are stationary; the reference optimiser (SciPy L-BFGS-B), started
   from a result of the kernel, does not find a lower value.
2. The result does not depend on the number of threads (identical output files).
3. Malformed and oversized input is rejected with the documented exit codes.
4. The same runs under AddressSanitizer and UndefinedBehaviorSanitizer (build_san/law_oracle).

usage: law_oracle_test.py            (needs build/law_oracle and build_san/law_oracle, see CMakeLists.txt)
"""
import os, subprocess, sys, tempfile
import numpy as np
import law_lp, law_cg

HERE = os.path.dirname(os.path.abspath(__file__))
RELEASE = os.path.join(HERE, 'build', 'law_oracle')
SANITIZE = os.path.join(HERE, 'build_san', 'law_oracle')
SAN_ENV = dict(ASAN_OPTIONS='detect_leaks=1:abort_on_error=0', UBSAN_OPTIONS='halt_on_error=1:print_stacktrace=1')


def problem(N, seed, count):
    """prices from a small linear programme, and random starting configurations"""
    L = law_lp.Law(N, seed); rs = L.rs
    for _ in range(3 * N):
        L.add(law_lp.haar_positions(N, rs), np.ones(N))
    for k in range(0, N // 2 + 1):
        L.add(*law_lp.lattice_config(N, k, rs, jitter=0.1))
    assert L.solve() is not None
    cands = [law_lp.lattice_config(N, int(k), rs, jitter=0.3) for k in rs.integers(0, N // 2 + 1, size=count)]
    return L, cands


def gradient_norm(L, x, d):
    """norm of the gradient of the reduced cost in the coordinates of the optimiser (the logits of the gaps)"""
    N = L.N; y = L.y[:-1]; j = np.arange(1, N); n = len(x); S = N - n * law_lp.GAP_MIN
    ph = np.exp(2j * np.pi * np.outer(j, x) / N); z = ph @ d
    gx = -(2 * np.real(np.conj(z)[:, None] * ph * (2j * np.pi * j[:, None] / N)) * y[:, None]).sum(axis=0) * d
    gaps = np.diff(np.append(x, x[0] + N)); sm = (gaps - law_lp.GAP_MIN) / S
    a = np.zeros(n); a[:-1] = np.cumsum(gx[::-1])[::-1][1:]
    return float(np.linalg.norm(S * (sm * a - sm * (sm @ a))))


def run(binary, text, threads=1, extra_env=None):
    with tempfile.TemporaryDirectory() as td:
        fin, fout = os.path.join(td, 'in.txt'), os.path.join(td, 'out.txt')
        open(fin, 'w').write(text)
        env = dict(os.environ, OMP_NUM_THREADS=str(threads), **(extra_env or {}))
        r = subprocess.run([binary, fin, fout], env=env, capture_output=True, text=True)
        return r.returncode, r.stderr.strip(), (open(fout).read() if os.path.exists(fout) else None)


def job_text(L, cands, iters=300):
    with tempfile.TemporaryDirectory() as td:
        path = os.path.join(td, 'job.txt')
        law_cg.write_job(path, L.N, L.y[:-1], [law_cg.normalise(x, d, L.N) for x, d in cands], iters)
        return open(path).read()


def main():
    failures = 0
    def check(name, ok, detail=''):
        nonlocal failures
        failures += 0 if ok else 1
        print(f'{"ok  " if ok else "FAIL"} {name}{"  " + detail if detail else ""}', flush=True)

    # 1. agreement with the Python reference
    for N, seed in ((16, 1), (32, 2), (64, 3)):
        L, cands = problem(N, seed, 60)
        res = law_cg.oracle(L, cands, threads=2, iters=5000, binary=RELEASE)      # run to convergence
        starts = [law_cg.normalise(x, d, N) for x, d in cands]
        cpp = np.array([L.reduced(x, d) for _, x, d in res])
        own = np.array([v + float((d == 1).sum()) / N - L.y[-1] for v, x, d in res])
        gaps = min(np.diff(np.append(x, x[0] + N)).min() for _, x, d in res)
        grad = max(gradient_norm(L, x, d) for _, x, d in res)
        legal = [i for i, (x, d) in enumerate(starts) if np.diff(np.append(x, x[0] + N)).min() >= law_lp.GAP_MIN + 1e-6]
        rise = max(cpp[i] - L.reduced(*starts[i]) for i in legal)
        polished = np.array([L.reduced(L.improve(x, d, iters=300), d) for _, x, d in res])
        check(f'N = {N}: value reported by the kernel equals the value recomputed in Python', np.abs(cpp - own).max() < 1e-9, f'max difference {np.abs(cpp - own).max():.1e}')
        check(f'N = {N}: all gaps at least {law_lp.GAP_MIN}', gaps >= law_lp.GAP_MIN - 1e-9, f'smallest gap {gaps:.6f}')
        check(f'N = {N}: no result is worse than its start', rise <= 1e-9, f'{len(legal)} starts with legal gaps')
        check(f'N = {N}: results are stationary', grad < 1e-4, f'largest gradient {grad:.1e}')
        gain = ((cpp - polished) / (1 + np.abs(cpp))).max()
        check(f'N = {N}: the reference optimiser does not improve the results', gain < 1e-7, f'largest relative gain {gain:.1e}')

    # 2. independence of the number of threads, and 4. sanitizers
    L, cands = problem(32, 5, 40); text = job_text(L, cands)
    outs = [run(RELEASE, text, threads=t) for t in (1, 2, 5)]
    check('the output does not depend on the number of threads', all(o[0] == 0 for o in outs) and outs[0][2] == outs[1][2] == outs[2][2])
    code, err, out = run(SANITIZE, text, threads=3, extra_env=SAN_ENV)
    check('sanitizer build: valid job runs without a report', code == 0 and err == '' and out is not None, err[:200])

    # 3. malformed input, with both builds
    N = L.N; prices = ' '.join(repr(float(v)) for v in L.y[:-1])
    def cand(n, xs, ds):
        return f'{n}\n{xs}\n{ds}\n'
    ones = ' '.join(['1'] * N); grid = ' '.join(str(float(i)) for i in range(N))
    cases = {
        'empty file': ('', 3),
        'text instead of numbers': ('abc def\n', 3),
        'period 1': (f'1 0.5 10 0\n\n', 3),
        'negative period': (f'-4 0.5 10 0\n1 1 1\n', 3),
        'period above the limit': (f'100000 0.5 10 0\n', 3),
        'gap not positive': (f'{N} 0.0 10 0\n{prices}\n', 3),
        'gap not a number': (f'{N} nan 10 0\n{prices}\n', 3),
        'iteration limit 0': (f'{N} 0.5 0 0\n{prices}\n', 3),
        'too many candidates': (f'{N} 0.5 10 99999999\n{prices}\n', 3),
        'too few prices': (f'{N} 0.5 10 0\n1.0 2.0\n', 3),
        'infinite price': (f'{N} 0.5 10 0\n' + prices.replace(prices.split()[0], 'inf', 1) + '\n', 3),
        'candidate missing': (f'{N} 0.5 10 1\n{prices}\n', 3),
        'more points than the period': (f'{N} 0.5 10 1\n{prices}\n' + cand(N + 1, grid + ' 0.5', ones + ' 1'), 3),
        'one point only': (f'{N} 0.5 10 1\n{prices}\n' + cand(1, '0.0', str(N)), 3),
        'mark 3': (f'{N} 0.5 10 1\n{prices}\n' + cand(N, grid, ones.replace('1', '3', 1)), 3),
        'mark 1.5': (f'{N} 0.5 10 1\n{prices}\n' + cand(N, grid, ones.replace('1', '1.5', 1)), 3),
        'marks do not sum to the period': (f'{N} 0.5 10 1\n{prices}\n' + cand(N - 1, ' '.join(grid.split()[:-1]), ' '.join(['1'] * (N - 1))), 3),
        'positions not sorted': (f'{N} 0.5 10 1\n{prices}\n' + cand(N, ' '.join(reversed(grid.split())), ones), 3),
        'position outside the period': (f'{N} 0.5 10 1\n{prices}\n' + cand(N, ' '.join(grid.split()[:-1]) + f' {float(N)}', ones), 3),
        'negative position': (f'{N} 0.5 10 1\n{prices}\n' + cand(N, '-1.0 ' + ' '.join(grid.split()[1:]), ones), 3),
        'no room for the minimum gap': (f'{N} 1.0 10 1\n{prices}\n' + cand(N, grid, ones), 3),
        'truncated positions': (f'{N} 0.5 10 1\n{prices}\n{N}\n0.0 1.0\n', 3),
        'no candidates (valid)': (f'{N} 0.5 10 0\n{prices}\n', 0),
        'coincident points (valid, raised to the minimum gap)': (f'{N} 0.5 10 1\n{prices}\n' + cand(N, ' '.join(['0.0'] * N), ones), 0),
    }
    for name, (text, expected) in cases.items():
        for label, binary, env in (('release', RELEASE, None), ('sanitizer', SANITIZE, SAN_ENV)):
            code, err, out = run(binary, text, extra_env=env)
            clean = 'ERROR' not in err and 'runtime error' not in err
            check(f'{label}: {name} -> exit code {expected}', code == expected and clean and ((out is not None) == (expected == 0)), f'got {code}: {err[:80]}' if code != expected or not clean else '')
    r = subprocess.run([RELEASE], capture_output=True, text=True)
    check('no arguments -> exit code 2', r.returncode == 2)
    r = subprocess.run([RELEASE, '/nonexistent/in.txt', '/nonexistent/out.txt'], capture_output=True, text=True)
    check('missing input file -> exit code 3', r.returncode == 3)
    with tempfile.TemporaryDirectory() as td:
        fin = os.path.join(td, 'in.txt'); open(fin, 'w').write(f'{N} 0.5 10 0\n{prices}\n')
        r = subprocess.run([RELEASE, fin, '/nonexistent/dir/out.txt'], capture_output=True, text=True)
        check('output file cannot be written -> exit code 4', r.returncode == 4)

    print(f'\n{"ALL TESTS PASSED" if failures == 0 else str(failures) + " TESTS FAILED"}')
    sys.exit(0 if failures == 0 else 1)


if __name__ == '__main__':
    main()
