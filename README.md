# Ancillary files

For the paper "More than 83.9% of the zeros of the Riemann zeta function are distinct and more
than 67.35% are simple and on the critical line" by Kristian Muri Knausgård. <https://www.alphaxiv.org/abs/2610.08965>

- `lean/` — the Lean 4 formalisation: the six theorems (developments `Distinct839/`,
  `Simple673/`, `Further/` and `Line889/`; statements from Mathlib alone in `Challenge839.lean`,
  `Challenge673.lean`, `ChallengeFurther.lean` and `Challenge889.lean`; proofs in the
  corresponding `Solution` files), the ceilings (`Ceilings/`), the patch `upstream_relax.patch`
  for the library `zeta23` on which everything builds, build instructions and the axiom audit
  (`lean/README.md`). This is the proof of record.
- `certificate/` — first window (Theorem 1.1): the frozen rational data of the seven-point
  inequality (`inputs.json`, Tables 7 to 9 of the paper) and reference programs: the kernel table
  builder (`build_kernel.py`, output `kernel_lower.bin`), the majorant check
  (`verify_majorant.py`), a branch and bound in Python (`verify_python.py`) and consistency
  checks of the data (`assemble.py`). The Lean development
  recomputes the table (identical in all 209,010 entries) and contains a verified port of the
  branch and bound; these programs are included for comparison. Result of the C++ verifier:
  `cpp_verification.json` (60,467,309 boxes, 30,233,655 accepted).
- `certificate_line/` — second window (Theorem 1.3): the same for the certificate of the critical
  line, an inequality for eight points without labels (`inputs.json`, with the entry
  `"points": 8`; Tables 10 and 11; table of 262,144 entries). There is no Python verifier
  for this certificate. Results: `cpp_verification.json` (535,332,163 boxes, 267,666,082
  accepted), `majorant_result.json`, `kernel_build.json`.
- `certificate_third/` — third window (Theorem 1.5): the same for the certificate of the zeros
  that are simple or on the critical line (`inputs.json`, Tables 12 and 13; table of 262,144
  entries). Results: `cpp_verification.json` (572,959,453 boxes, 286,479,727 accepted),
  `majorant_result.json`, `kernel_build.json`.
- `verifier/` — the reference verifier of the local inequality for the three certificates, in
  C++23 (`verify.cpp`, built for frames of seven points and for frames of eight), with validated
  input and tests. See `verifier/README.md`.
- `limits/` — scripts and data for Section 7 (limits of the method): ceilings by ball arithmetic
  for both windows and for the two earlier windows, see `limits/README.md` and
  `limits/certified.log`; `lean_ceiling_data.json` holds the trial states and weights used in the
  Lean proofs of the ceilings.
- `law/` — the ceiling for all windows (Section 7.6): certified laws of period 16 to 256
  (`law{N}_certified.json`, exact rational data), the second stage of the search for period 256 with the law of Proposition 7.8 (`deep/law256_deep_certified.json`), the
  two programs that verify them (`law_certify.py`, `law_check_iv.py`), and the programs that
  found them (`law_cg.py`, the C++ kernel `law_oracle.cpp`, the pipeline `run_all.sh`), with
  tests, logs and a record of the run. See `law/README.md`.

To run the reference programs (not needed for the proof): `verifier/README.md` says how to
build and run the C++ verifier, and `verifier/run_certificates.sh` writes the three files
`cpp_verification.json`. `verify_python.py` (first certificate only) does the same search in
Python and needs `numba`. `build_kernel.py` rebuilds `kernel_lower.bin`, and `verify_majorant.py`
writes `majorant_result.json`.

`CHECKSUMS.sha256` holds the SHA-256 checksum of every file here except the six settings files
named next; `sha256sum -c CHECKSUMS.sha256` checks a copy.

The copy attached to the arXiv version of the paper lacks six files: `.clang-format` and
`.clang-tidy` in `verifier/`, `law/` and `law/deep/`, the settings of the code formatter and of
the linter for the three C++ programs. arXiv removes files whose names begin with a period.
They are in the repository, and nothing else differs between the two copies.

## Licence

The files here are under the MIT licence (`LICENSE`), except the directory `lean/`, which is
under the Apache License, Version 2.0 (`lean/LICENSE`). That is the licence of the Lean library
`zeta23` of <https://github.com/anthropics/formal-math> (Copyright 2026 Anthropic, PBC), on which
the proofs build and from which the directory contains material: a patch to fourteen files of
the library, definitions repeated in the statement files, and lines of proofs. `lean/NOTICE`
lists this material and reproduces the library's notice file. The library itself is not included.
