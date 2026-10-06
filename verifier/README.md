# Reference verifier of the local inequality, in C++23

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: the programs and this text were drafted with AI systems (OpenAI Codex and Claude,
Anthropic), under the direction of the author, who is responsible for their content.

## What is here

The paper proves three local inequalities with the help of a computer: for seven consecutive
points with labels (first and third window) and for eight consecutive points (second window, for
the critical line). The proof of record is in Lean: the checker there is verified, and nothing
in the paper depends on the programs in this folder.

`verify.cpp` is a reference program for the same computation. It reads the frozen integer data
of a certificate and the table of lower bounds for the squared kernel, and decides the
inequality for all frames by branch and bound over the gaps, in exact integer arithmetic. The
number of points of a frame is a compile-time setting (`VERIFY_POINT_COUNT`); the build makes
two programs from the one source, `verify` for seven points and `verify8` for eight. The comment
at the top of the file states the inequality, the tests applied to a box and the formats of the
input.

`verify.cpp` runs the same search as the Lean checker, with the same tests in the same order,
so the two visit the same boxes. The data are read at run time and validated; the table is
decoded independently of the byte order of the machine; and besides the conditions on local data
of the paper the program checks that the functions B_r vanish at their first and last knot,
which the search uses and all three certificates satisfy.

Files:

- `verify.cpp` — the program; `CMakeLists.txt`, `.clang-format`, `.clang-tidy` — build, format
  and lint settings.
- `make_parameters.py` — writes the parameter file of the program from `inputs.json` of a
  certificate; the number of points is the entry `points` there (seven if there is none).
- `verify_test.py` — tests; log `test_verify.log`.
- `run_certificates.sh` — runs the program for the right number of points on each of the three
  certificates and writes its result line into each certificate folder
  (`cpp_verification.json`).

## Results

All three certificates of the paper are accepted, with the counts of boxes stated in the paper
and in `../lean/README.md`:

| | first window (`../certificate/`) | second window (`../certificate_line/`) | third window (`../certificate_third/`) |
|---|---|---|---|
| points of a frame, program | 7, `verify` | 8, `verify8` | 7, `verify` |
| boxes examined | 60,467,309 | 535,332,163 | 572,959,453 |
| boxes accepted | 30,233,655 | 267,666,082 | 286,479,727 |
| accepted by the span test or the basic test | 21,157,274 | 202,511,130 | 256,891,820 |
| accepted by the affine test | 9,076,381 | 65,154,952 | 29,587,907 |
| largest number of boxes waiting | 49 | 63 | 68 |

The five numbers are those of the normal build, and they are the content of the files
`cpp_verification.json` in the certificate folders. The counting version of the Lean checker gives
the same numbers of boxes examined and accepted (`../lean/README.md`), and so does the Python
program `../certificate/verify_python.py` for the first window.

`test_verify.log`: 106 checks, all passed. It is the output of `verify_test.py` without the
options for the full runs.

## Build and run

Requirements: a C++23 compiler (g++ 15 was used), CMake, Python 3.

    cmake -S . -B build && cmake --build build
    python3 make_parameters.py ../certificate/inputs.json first_window.txt
    build/verify first_window.txt ../certificate/kernel_lower.bin
    python3 make_parameters.py ../certificate_line/inputs.json second_window.txt
    build/verify8 second_window.txt ../certificate_line/kernel_lower.bin

    cmake -S . -B build_san -DVERIFY_SANITIZE=ON && cmake --build build_san
    python3 verify_test.py                               # quick tests, both builds
    python3 verify_test.py --full --full-sanitizer       # and the three certificates, both builds
    ./run_certificates.sh                                # the result files of the three certificates

The program prints one line, for example

    {"status":"PASS_COB_CONTINUUM","nodes":60467309,"leaves":30233655,"basic":21157274,"affine":9076381,"max_stack":49}

`nodes` is the number of boxes examined, `leaves` the number accepted (`basic` by the span test or
the basic test, `affine` by the affine test), and `max_stack` the largest number of boxes waiting.
Exit codes: 0 the inequality is
verified; 1 a box could not be decided (status `UNRESOLVED`, and the box is printed); 2 wrong
usage; 3 the input is rejected; 5 an internal limit is reached.

## How the program is written

`verify.cpp` follows the rules stated at the top of the file, the same as for the other C++
program of this repository (`../law/law_oracle.cpp`): no raw owning pointers, no pointer
arithmetic, no C arrays or casts; all input validated and limited in size; all memory allocated
before the search starts; bounded loops, no recursion, a stack of boxes of fixed capacity; no
floating-point arithmetic; errors as values (`std::expected`), no `throw`. The build keeps the
bounds checks of the standard library on (`_GLIBCXX_ASSERTIONS`) and treats a strict set of
warnings as errors. The file is formatted with `.clang-format` and is clean under `clang-tidy`
with the checks and naming rules of `.clang-tidy`.

One compiler extension is used: the 128-bit integer type of GCC and Clang, for products that do
not fit in 64 bits. ISO C++23 has no such type.

Integer ranges: grid coordinates are 32-bit and values 64-bit. The limits on the input exclude
overflow of the 32-bit sums, and a bound on the 64-bit intermediates is checked before the search.
In addition, the tests below are run with the sanitizer build, which stops at any signed
overflow and any access out of bounds; among them is a search of 4.7 million boxes for frames of
eight points (a false certificate, which is not accepted).

## Tests

`verify_test.py` checks, with the normal and with the sanitizer build:

- 41 kinds of malformed input, input outside the limits, and data that violate a condition on
  local data are rejected with exit code 3 and the message for that reason;
- data for frames of eight points are rejected by the program for seven points, and data for
  seven points by the program for eight;
- false certificates are not accepted: with the weights of a certificate reduced by one tenth or
  halved, or with its functions B_r removed, the program ends with exit code 1;
- easier certificates (a larger rate alpha) are accepted with the recorded counts;
- with `--full` and `--full-sanitizer`, the three certificates of the paper are accepted with the
  counts of boxes stated in the paper.

## Versions used

c++ (Ubuntu 15.2.0-4ubuntu4) 15.2.0; cmake version 3.31.6; clang-tidy and clang-format 20.1.8 (LLVM); Python 3.13.7; aarch64, Linux-6.17.0-41-generic-aarch64-with-glibc2.42. Build type Release (`-O3 -DNDEBUG`), with `-D_GLIBCXX_ASSERTIONS`; sanitizer build `-O1 -g -fsanitize=address,undefined`. The runs were made on 6 October 2026 from the files in this folder (checksums in `../CHECKSUMS.sha256`). On this machine the normal build needs three to ten minutes for the first and for the third certificate and about 45 minutes for the second; the sanitizer build is several times slower.
