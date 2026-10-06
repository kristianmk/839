# A law of periodic configurations: the ceiling for all windows (Section 7.6)

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: the programs and this text were drafted with Claude (Anthropic), an AI system,
under the direction of the author, who is responsible for their content.

## What is here

Section 7.6 of the paper bounds what the method can give with any window. The bound needs a
*law of period N with error τ*: a finitely supported probability law on N-periodic
configurations of distinct points with labels 1 (simple) or 2 (double) and total multiplicity N
per period, with rational weights, whose form factor

    S(j) = (1/N) Σ_c w_c |Σ_i d_i exp(2πi j ξ_i / N)|²

satisfies |N S(j) − j| ≤ τ for 0 < j < N. With p the mean share of simple points, every such
law gives the two bounds of Theorem 7.7. The idea and the inequality behind it are due to
Alpöge and Furman (arXiv:2608.13637, Section 7.2). Their law of period 256 is not public. This
folder contains our own computation of such laws, made from the description in their paper,
with all data and programs, and the verification of the properties that the paper uses.

Results (certified; values rounded up, the smallest gap rounded down). Bound (a) is the ceiling
for distinct zeros and bound (b) the ceiling for simple zeros on the critical line, both for
windows with V(f) ≤ 10 B(f) (Theorem 7.7, Corollary 7.9, Table 4 of the paper):

| Period N | Share of simple points p | (1 + p)/2 | Bound (a) | Bound (b) | Smallest gap | Rounds of the search |
|---|---|---|---|---|---|---|
| 16 | 0.6828368 | 0.8414184 | 0.84346 | 0.68692 | 1.0022 | 101 |
| 32 | 0.6820902 | 0.8410451 | 0.84157 | 0.68313 | 1.0043 | 135 |
| 64 | 0.6818908 | 0.8409454 | 0.84108 | 0.68215 | 1.0012 | 531 |
| 128 | 0.6818404 | 0.8409202 | 0.84096 | 0.68191 | 0.9985 | 1076 |
| 256 | 0.6818290 | 0.8409145 | 0.84093 | 0.68185 | 0.9981 | 2150 |
| 256, second stage (`deep/`) | 0.6818277 | 0.8409139 | 0.84093 | 0.68185 | 0.9981 | 700 more |

For comparison, the Lean library of Alpöge and Furman records p₀ = 0.68182868746… for their law
of period 256, which gives the bound 0.84093. After the first stage of our search the share of
simple points is larger than p₀ by less than 3.1·10⁻⁷. A second stage, which searches further
from that law with chains of moves that change the labels (folder `deep/`, with its own README),
ends at a law whose share is smaller than p₀ by more than 1.06·10⁻⁶. The bound is 0.84093 for all
three laws.

The law of the second stage, `deep/law256_deep_certified.json`, is the law of Proposition 7.8.

## What is proved, and by what

The properties used in the paper are finite statements about the files `law{N}_certified.json`
and `deep/law256_deep_certified.json`, which hold exact rational points (twelve decimals) and exact rational weights (denominator
10^60):

- labels in {1, 2}; total multiplicity N in every configuration; points distinct, in [0, N);
- weights nonnegative, with sum exactly 1;
- |N S(j) − j| ≤ 10^-30 for 0 < j < N;
- the share of simple points p, an exact rational number, and the smallest gap.

Two programs verify them independently:

- `law_certify.py` (python-flint: FLINT/Arb ball arithmetic at 600 bits, exact rationals). It
  also produces the certified file from the output of the search: it rounds the points to
  rationals, recomputes the weights for the rounded points from the N linear equations in high
  precision, rounds them to rationals with sum 1, and then verifies. Logs: `certify{N}.log`, `deep/certify256_deep.log`.
- `law_check_iv.py` (mpmath interval arithmetic; no code in common with the first, and it reads
  only the certified file). Logs: `check{N}.log`, `deep/check256_deep.log`.

Nothing in the paper depends on the correctness of the search programs below. A law is a
witness: however it was found, the two programs above check it.

## How the laws were found

For a finite set of configurations the least p is the value of a linear programme with N
equations. A further configuration improves it if its reduced cost for the current dual
variables is negative, and finding such a configuration is a ground-state problem for labelled
points with a pair interaction given by the dual variables. The search alternates between the
two (column generation):

- `law_cg.py` — the search. The linear programme is kept in HiGHS (`highspy`) and solved again
  from the previous basis after new columns are added. Candidates are perturbations of the
  configurations in use and neighbours of them (two simple points merged, a double point split,
  a double point moved). Each period starts from configurations of the previous period placed
  one after the other. The reduced cost of every candidate is recomputed in Python before it is
  used. Logs: `law{N}.log`; results: `law{N}.json` (floating point).
- `law_oracle.cpp` — the local optimisation of the candidates (L-BFGS with all gaps kept above
  0.5 by the parametrisation), in C++23, in parallel over the candidates with OpenMP.
- `law_lp.py` — statement of the problem and a reference implementation in pure Python
  (SciPy). The tests compare the C++ kernel with it.
- `run_all.sh` — the pipeline that produced the files here: build, then search and
  certification for N = 16, 32, 64, 128, 256, then the independent check of all five.
- `deep/` — the second stage for period 256: its programs, tests, results and README.

The search is a heuristic and runs in floating point. We do not claim that the laws are optimal
for their period.

## The C++ kernel

`law_oracle.cpp` follows the rules stated at the top of the file: no raw owning pointers, no
pointer arithmetic, no C arrays or casts; all input validated and limited in size; all memory
allocated before the optimisation starts; bounded loops, no recursion; errors as values
(`std::expected`), no `throw`; threads share only read-only data. The build
(`CMakeLists.txt`) keeps the bounds checks of the standard library on (`_GLIBCXX_ASSERTIONS`)
and treats a strict set of warnings as errors. The file is formatted with `.clang-format` and is
clean under `clang-tidy` with the checks and naming rules of `.clang-tidy`.

`law_oracle_test.py` (log `test_oracle.log`) checks, for periods 16, 32 and 64: that the value
reported by the kernel equals the value recomputed in Python; that all gaps respect the bound;
that no result is worse than its start; that the results are stationary; and that the reference
optimiser, started from a result, does not improve it. It also checks that the output does not
depend on the number of threads, that 22 kinds of malformed or oversized input are rejected with
the documented exit code and two boundary inputs are accepted, and it repeats these runs with a
build under AddressSanitizer and UndefinedBehaviorSanitizer.

## Reproducing

Requirements: Python 3 with numpy, scipy, highspy, python-flint and mpmath; a C++23 compiler
with OpenMP (g++ 15 was used); CMake.

    PYTHON=python3 THREADS=9 ./run_all.sh            # everything; several hours for period 256
    python3 law_certify.py law256.json out.json      # certify one law again
    python3 law_check_iv.py law256_certified.json    # independent check of one certified law

    cmake -S . -B build_san -DLAW_SANITIZE=ON && cmake --build build_san
    python3 law_oracle_test.py                       # tests of the kernel

With the same compiler, libraries and processor type the search is deterministic (fixed seed;
the kernel's output does not depend on the number of threads). On another machine the
floating-point search can take a different path and end at slightly different laws; each of them
is certified in the same way.

## Where the files here come from

The programs were committed first, and the files here were then produced by `run_all.sh` in a
clean export of that commit. `run_manifest.json` (written by `law_manifest.py`) records the run:
the commit, every source file with its SHA-256 checksum and its git blob id, the binary, the
compiler flags, the versions and the machine, and the checksums of all results. The commit named
there is one of the author's working repository, not of the public one. What connects the two
is the git blob id: it depends only on the content of a file, so `git ls-tree -r HEAD` in any
repository that holds these files shows the same ids.

The run was made twice on 4 October 2026: once in the working folder and once in the clean
export. `compare.txt` is the comparison: the five laws, the five certified laws and the binary
are identical byte for byte, and the fifteen logs are identical apart from the timing columns.

Versions used: c++ (Ubuntu 15.2.0-4ubuntu4) 15.2.0; cmake version 3.31.6; build type Release (`-O3 -DNDEBUG`, `-march=native`, `-fopenmp`, `-D_GLIBCXX_ASSERTIONS`); Python 3.13.7 with numpy 2.5.3, scipy 1.18.1, highspy 1.15.1, python-flint 0.9.0, mpmath 1.4.1; aarch64, 12 cores, Linux-6.17.0-41-generic-aarch64-with-glibc2.42. Period 256 took about an hour and a half for the search (nine threads), two minutes for the certification and a quarter of an hour for the independent check.
