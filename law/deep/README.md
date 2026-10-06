# Second stage of the search: the law of Proposition 7.8

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: the programs and this text were drafted with Claude (Anthropic), an AI system,
under the direction of the author, who is responsible for their content.

## What is here

The first stage (`../law_cg.py`, `../law_oracle.cpp`) ends, for period 256, at a law with share of
simple points p = 0.6818290. Its candidates come from the configurations in use by small
perturbations and by single changes of the marks. This folder contains a second stage that
searches further from that law:

- `law_deep.cpp` — from each configuration in use it runs a chain of moves (a double point is
  moved, two simple points are merged, a double point is split), relaxes the positions after
  every move, and accepts a move if the cost goes down, or with the Metropolis probability if it
  goes up. C++23, with the kernel classes and the design rules of `../law_oracle.cpp`. The chains
  are reproducible: chain k draws from a generator seeded with the seed and k, so the result does
  not depend on the number of threads.
- `law_deep.py` — the linear programme as in the first stage (HiGHS), with `law_deep` as the
  source of new configurations. The cost of every configuration is recomputed in Python before
  it is used.
- `run_deep.sh` — the pipeline of this stage: build, 700 rounds from `../law256.json`,
  certification with `../law_certify.py`, independent check with `../law_check_iv.py`.
- `law_deep_test.py` (log `test_deep.log`), `deep_manifest.py`, `CMakeLists.txt`, `.clang-format`,
  `.clang-tidy`.

Like the first stage this is a heuristic in floating point, and nothing in the paper depends on
its correctness: the law it ends with is a witness, and the two certification programs check it.
We do not claim that the law is optimal for its period.

## Result

Started from `../law256.json` (p = 0.6818290, the last law of the first stage), 700 rounds:

| | Share of simple points p | (1 + p)/2 | Bound (a) | Bound (b) | Smallest gap | Configurations |
|---|---|---|---|---|---|---|
| first stage | 0.6818290 | 0.8409145 | 0.84093 | 0.68185 | 0.9981 | 256 |
| second stage | 0.6818277 | 0.8409139 | 0.84093 | 0.68185 | 0.9981 | 256 |

(values rounded up, the smallest gap rounded down; bounds (a) and (b) as in `../README.md`). The
certified law is `law256_deep_certified.json`: exact rational points and weights, error at most
10^-30 (the independent check finds it below 2.1e-56). Its share of simple points is
p = 0.681827619524…, which is smaller than the value p₀ = 0.68182868746… recorded in the Lean
library of Alpöge and Furman for their law of period 256, by more than 1.06·10⁻⁶. This is the law
of Proposition 7.8 of the paper. The two bounds are unchanged at the precision of the paper.

Files: `law256_deep.json` (floating point, output of the search), `law256_deep.log` (one line per
round), `law256_deep_certified.json`, `certify256_deep.log` (`../law_certify.py`),
`check256_deep.log` (`../law_check_iv.py`).

## Tests

`law_deep_test.py` checks, for periods 16, 32 and 64: that the cost reported for every
configuration equals the cost recomputed in Python; that every configuration is legal (marks 1 or
2 with sum N, positions in order, all gaps at least the minimum); that every chain returns between
one and the requested number of configurations, and that its best one is not worse than its
start. It checks that the output does not depend on the number of threads and does depend on the
seed, that 28 kinds of malformed or oversized input are rejected with the documented exit code and
three boundary inputs are accepted, and it repeats these runs with a build under AddressSanitizer
and UndefinedBehaviorSanitizer. The file is formatted with `.clang-format` and is clean under
`clang-tidy` with the checks and naming rules of `.clang-tidy`.

## Reproducing

Requirements as for the first stage (`../README.md`).

    PYTHON=python3 THREADS=9 ./run_deep.sh                 # about two hours
    cmake -S . -B build_san -DLAW_SANITIZE=ON && cmake --build build_san
    python3 law_deep_test.py                               # tests of law_deep

With the same compiler, libraries and processor type the search is deterministic (fixed seed).
On another machine it can take a different path and end at a slightly different law, which is
certified in the same way.

## Where the files here come from

As for the first stage: the programs were committed first (commit `0619bc2` of the author's
working repository), and the files here were produced by `run_deep.sh` in a clean export of that
commit, on 5 October 2026 with six threads. `run_manifest.json` (written by `deep_manifest.py`)
records the run: the commit, every source file with its SHA-256 checksum and git blob id, the
law it started from, the binary, the compiler flags, the versions, the machine and the checksums
of the results. The starting law has the checksum recorded for `law256.json` in
`../run_manifest.json`.

The same search had been run once before in the working folder, with nine threads and the same
code (the header comments of two files were written afterwards). `compare.txt` compares the two
runs: the law, the certified law and the certification log are identical byte for byte, and the
search log is identical apart from the timing columns.
