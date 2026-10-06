# Lean 4 proofs for "More than 83.9% of the zeros of the Riemann zeta function are distinct and more than 67.35% are simple and on the critical line"

This directory extends the library `zeta23` (subdirectory `zeta23/` of
<https://github.com/anthropics/formal-math>, commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`,
Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`).

## The statements

```lean
theorem distinct_zeros_839 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1645064 / 1960733 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T
theorem simple_zeros_678 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1329395 / 1960733 - ε) * (Ncount 0 T : ℝ) ≤ Nsimple 0 T
theorem simple_critical_zeros_673 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1669159 / 2478195 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T
theorem average_simple_and_critical_8367 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2073677 / 2478195 - ε) * (Ncount 0 T : ℝ) ≤ ((Nsimple 0 T : ℝ) + (N0mult 0 T : ℝ)) / 2
theorem simple_or_critical_8891 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3376433 / 3797325 - ε) * (Ncount 0 T : ℝ) ≤ NsimpleOrLine 0 T
theorem simple_or_critical_8893 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (50652159 / 56956375 - ε) * (Ncount 0 T : ℝ) ≤ NsimpleOrLine 0 T
```

`Ncount 0 T` is the number of zeros of Mathlib's `riemannZeta` with real part in `(0, 1)` and
imaginary part in `(0, T]`, counted with multiplicity (order of vanishing). `Ndist 0 T` counts the
distinct ones, `Nsimple 0 T` those of multiplicity exactly 1, and `N0simple 0 T` those of
multiplicity exactly 1 with real part `1/2`. `N0mult 0 T` counts, with multiplicity, those with
real part `1/2`, and `NsimpleOrLine 0 T` counts, with multiplicity, those that have multiplicity
1 or real part `1/2`. The first three statements are Theorem 1.1, Corollary 1.2 and Theorem 1.3
of the paper: the lower limits of `N_d/N`, `N_s/N` and `N_0^s/N` are at least `0.8390045…`,
`0.6780091…` and `0.6735382…`. The next two are Theorem 1.4: the lower limits of
`(N_s + N_0)/(2N)` and of `N_{s∪0}/N` are at least `0.8367691…` and `0.8891609…`. The last is
Theorem 1.5: with a third window the lower limit of `N_{s∪0}/N` is at least `0.8893150…`.

The ceilings (Propositions 7.2 and 7.3 of the paper), in the namespace `Ceilings`:

```lean
theorem ceiling_range6  : PairCert 6 x₁ x₂ b → 0 ≤ b → 0 < 2 - 2 * x₁ + x₂ →
    (3 - energyC + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83916 / 100000
theorem ceiling_range8  : PairCert 8 x₁ x₂ b → … < 83943 / 100000
theorem ceiling_range10 : PairCert 10 x₁ x₂ b → … < 83957 / 100000
theorem ceiling_all     : PairCertAll x₁ x₂ b → … < 83998 / 100000
theorem ceiling_line_range7 : PairCert1 7 x b → 0 ≤ b → x < 1 →
    (2 - energyCLine - b) / (1 - x) < 67357 / 100000
theorem ceiling_line_all    : PairCert1All x b → … < 67383 / 100000
```

`PairCert s x₁ x₂ b` says: there is a constant `C₃` such that every `17/20`-separated labelled
configuration with spread at most `R` has pair energy within index distance `s` at least
`x₁·n₁ + x₂·n₂ − b·R − C₃` (`PairCertAll`: all pairs; `PairCert1`, `PairCert1All`: simple points
and the second window). `energyC` and `energyCLine` are the energy constants `C(f)` of the two
windows, proved equal to the constant `kappa 1` of the respective main proof. In
`ChallengeCeilings.lean` the two constants are defined as the paper defines them,
`C(f) = ∫ f² + ∬ |s − t| f(s) f(t) ds dt` (`windowEnergy`), and `SolutionCeilings.lean` proves
that they are `energyC` and `energyCLine` (`energyFirst_eq`, `energySecond_eq`) and gives their
closed forms (`energyFirst_closed`, `energySecond_closed`). The change of variables behind this,
`2 ∫₀¹ r (f⋆f)(r) dr = ∬ |s − t| f(s) f(t) ds dt` for every continuous `f`, is
`Ceilings.two_mul_integral_mul_vConv_eq` in `Ceilings/EnergyIntegral.lean`.

## What to read

- `Challenge839.lean`, `Challenge673.lean`, `ChallengeFurther.lean`, `Challenge889.lean`: the six
  theorems stated from Mathlib alone (the definitions and the statements, with `sorry` by design).
  `ChallengeCeilings.lean` does the same for the six ceilings. These are the only files one has to
  trust to know what is claimed.
- `Solution839.lean`, `Solution673.lean`, `SolutionFurther.lean`, `Solution889.lean`,
  `SolutionCeilings.lean`: the same statements, proved.
- `Distinct839/Defs.lean`, `Simple673/Defs.lean`, `Line889/Defs.lean`: the three windows, the
  kernels and the frozen certificate tables. `Spec.lean`, `Spec2.lean` in each: the statements of the layers.
  `Compose.lean`: how the layers combine. `Ceilings/Distinct/Defs.lean`, `Ceilings/Line/Defs.lean`:
  the certificate predicates.

## The developments

`Distinct839/` (Theorem 1.1 and Corollary 1.2; 72 files, 13,317 lines):

| directory | lines | main result |
|---|---|---|
| `Kernel/` | 1382 | the kernel `K`, a table of lower bounds for `K²` computed in exact arithmetic and proved sound (`kTab_sound`, `kTabArray_sound`), `betaBound` |
| `Local/` | 2744 | the branch-and-bound checker (`Checker.lean`, no Mathlib import, compiled), its soundness (`localInequality_of_check`), the evaluation (`RunAll.lean`), `localInequality`, kernel spot checks |
| `Transfer/` | 977 | `transfer : LocalInequality → TransferStatement` (sum over frames, telescoping) |
| `Gram/` | 1250 | `gramEnergy : BetaBound → TransferStatement → GramEnergyStatement` (matching, pinching, pair blocks) |
| `Majorant/` | 1224 | the two-sinc majorant: `majorantPointwise`, `lMajBound`, `separatedBound` |
| `Window/` | 1223 | the window lies in the window class of `zeta23` (`admWindow_vProf`) |
| `WindowMoments/` | 551 | moments of the realised window, `tendsto_cRatio_vProf` |
| `WindowSide/` | 359 | `admFamily_vProf`, `windowZeroSide_vProf`, `eventually_a_vProf` |
| `ZetaMoments/` | 298 | trace and second moment of the zeta operator for an admissible profile (`gzMoments_atV_zeta`) |
| `Constant/` | 478 | the energy constant `kappa lam = A/lam + lam·B`, `exists_kappa_le` |
| `ZeroKernel/` | 1094 | Gram entries of zeros on the line (`gramData`) |
| `Assembly/` | 1289 | seam, counting and asymptotics (`distinct839_of`) |

`Simple.lean` (72 lines) derives the corollary for simple zeros (`two_mul_Ndist_le`,
`simple_of_distinct`, `simple_zeros_678`).

`Simple673/` (Theorem 1.3; 57 files, 9,981 lines). The same chain for the second window, which
has ten cosine terms, at the clipping level 2, with a local inequality for frames of eight
points (seven gaps). It imports the parts of `Distinct839` that do not
depend on the window or on the labels (Taylor bounds, trigonometric enclosures, pinching,
matching, the edge count, `ZetaMoments/`).

| directory | lines | main result |
|---|---|---|
| `Kernel/` | 988 | `kIntegral`, `kTab_sound`, `kTabArray` (262,144 entries) with `kTabArray_sound`, `betaBound` |
| `Local/` | 3131 | the checker for the second certificate (frames of eight points), `localInequality_of_check`, the search in parts (`checkAllPar`, `localInequality_of_checkPar`), `RunAll.lean`, `localInequality`, kernel spot checks |
| `Transfer/` | 936 | `transfer`, and `Transfer.transfer_range7` (only pairs at index distance at most seven) |
| `Gram/` | 479 | `gramEnergy`: the Gram bound for simple points at level 2 (`C = 44`, `η₀ = 1/100`) |
| `Majorant/` | 970 | `majorantPointwise`, `lMajBound`, `separatedBound` (`γ₀ = 13/20`) |
| `Window/` | 662 | `windowStatement` |
| `WindowSide/` | 426 | `windowSide`, `windowMoments` |
| `Constant/` | 431 | `kappaStatement`, `kappa_eq`, bounds for `Aconst + Bconst` |
| `ZeroKernel/` | 761 | `gramDataLayer` |
| `Assembly/` | 708 | the count at level 2 for `N0simple` (`assembly`) |

`Further/` (Theorem 1.4; 12 files, 1,813 lines). No new computation: the first bound uses the
layers of `Simple673` and the second those of `Distinct839`.

| file | lines | main result |
|---|---|---|
| `Defs.lean` | 44 | the counts `N0mult`, `Nsimple`, `NsimpleOrLine` |
| `Threshold.lean` | 179 | the threshold inequality with two levels (`threshold2_eig_phiC`: Lemma 6.1 of the paper), `seam_block2` |
| `Certificate.lean` | 94 | `count_certificate`: from the seam inequality with general coefficients to a bound for a count |
| `Counting.lean` | 224 | additivity and edge bounds for the new counts; their identification for the zeros of `riemannZeta` |
| `Line/` | 552 | the average at the level 2 (`avg_bound_family`), from the certificate of the second window |
| `Dist/` | 628 | simple or on the line, clipping level 67/20 and tangent level 27/8 (`sl_bound_family`), from the certificate of the first window |
| `Main.lean` | 92 | `average_simple_and_critical_8367`, `simple_or_critical_8891` and their forms `…_of_local` |

`Line889/` (Theorem 1.5; 54 files, 9,122 lines). The chain of `Simple673` for the third window,
with the count of `Further/Dist` (the threshold inequality with two levels) in place of the count
of simple zeros on the line. It imports the same parts of `Distinct839` as `Simple673` does, and
from `Further` the definitions, the threshold inequality and the counting lemmas.

| directory | lines | main result |
|---|---|---|
| `Kernel/` | 978 | `kIntegral`, `kTab_sound`, `kTabArray` (262,144 entries) with `kTabArray_sound`, `betaBound` (`β = 3/50`) |
| `Local/` | 2847 | the checker for the third certificate, `localInequality_of_check`, `RunAll.lean`, `localInequality`, kernel spot checks |
| `Transfer/` | 608 | `transfer`, `Transfer.transfer_range6` |
| `Gram/` | 474 | `gramEnergy`: the Gram bound for simple points at level 2 |
| `Majorant/` | 971 | `majorantPointwise`, `lMajBound`, `separatedBound` (`γ₀ = 61/100`) |
| `Window/` | 642 | `windowStatement` |
| `WindowSide/` | 420 | `windowSide`, `windowMoments` |
| `Constant/` | 318 | `kappaStatement`, `kappa_eq`, bounds for `Aconst + Bconst` |
| `ZeroKernel/` | 725 | `gramDataLayer` |
| `Assembly/` | 655 | the count of the zeros that are simple or on the line, clipping level 2 and tangent level 27/8 (`assembly`) |

`Ceilings/` (Propositions 7.2 and 7.3; 23 files, 3,394 lines): `EnergyIntegral.lean` (the
energy constant as a double integral), `Periodic.lean` (a certificate
applied to `M` periods of a periodic state), `Trig.lean`, `KernelBound.lean`, `State.lean`
(rational trial states and verified upper bounds for `K²` on `ℚ`), `Mixture.lean` (the weighted
sum), `Distinct/` and `Line/` (the two windows; `Range6`, `Range8`, `Range10`, `All` for the first and
`Range7`, `All` for the second), and the
bridges: `Distinct/Gram.lean`, `GramBridge.lean` (`GramCert.toPairCertAll`: an inequality of the
Gram form implies the all-pairs hypothesis), `Distinct/PaperCert.lean`, `Line/PaperCert.lean`
(`paper_certificate`, `line_certificate`: the certificates of the paper are of range six and of
range seven).

## Axioms

`axioms.txt` is the output of the five scripts `scripts/PrintAxioms*.lean` and of the five
comparison files `scripts/Compare*.lean`.

- `distinct_zeros_839`, `simple_zeros_678`: `propext`, `Classical.choice`, `Quot.sound` and
  `Distinct839.Local.check_passes._native.native_decide.ax_1_1`.
- `simple_critical_zeros_673`: the three standard axioms and
  `Simple673.Local.check_passes._native.native_decide.ax_1_1`.
- `average_simple_and_critical_8367`: the three standard axioms and the axiom of the second search
  (`Simple673.Local…`). `simple_or_critical_8891`: the three standard axioms and the axiom of the
  first search (`Distinct839.Local…`). Their forms `…_of_local`, the two-level threshold
  inequality and the counting lemmas: the three standard axioms only.
- `simple_or_critical_8893`: the three standard axioms and
  `Line889.Local.check_passes._native.native_decide.ax_1_1`, the axiom of the third search. Its
  forms `…_of_local` and `…_of_layers`: the three standard axioms only.
- The six ceilings, `GramCert.toPairCertAll`, the identifications of the energy constants, their
  closed forms and the change of variables `two_mul_integral_mul_vConv_eq`:
  the three standard axioms only. `paper_certificate` and `line_certificate` inherit the axiom of
  the respective search.

Each of the three extra axioms is recorded by `native_decide` for one evaluation: the statement
`checkAll kTabArray = true` of `Distinct839/Local/RunAll.lean` and of `Line889/Local/RunAll.lean`,
and the statement `checkAllPar kTabArray 32 96 = true` of `Simple673/Local/RunAll.lean`. The
table is evaluated by Lean's interpreter and the checker by compiled code. `checkAllPar` is the
search of `checkAll` cut into parts: the boxes that are left after 32 splits are dealt out to 96
parts, and compiled code examines each part on a thread of its own;
`localInequality_of_checkPar` proves the local inequality from it for every depth and every
number of parts. This trusts the Lean compiler, interpreter and runtime for these three
computations. Everything else is checked by
the kernel: the theorems `…_of_local : LocalInequality → …`, the soundness theorems of the
checkers (`localInequality_of_check`, `localInequality_of_checkPar`) and of the tables
(`kTabArray_sound`) depend on the three
standard axioms only.

Supporting checks of the three evaluations:

| | first search | second search | third search |
|---|---|---|---|
| table written to a file against the reference `kernel_lower.bin` | identical, 209,010 entries | identical, 262,144 entries | identical, 262,144 entries |
| boxes visited / accepted by the counting driver (`localcheck`, `localcheck673`, `localcheck889`) | 60,467,309 / 30,233,655 | 535,332,163 / 267,666,082 | 572,959,453 / 286,479,727 |
| the same counts in the reference programs | C++ and Python | C++ | C++ |
| boxes checked by the kernel itself (`Local/SpotChecks.lean`, `decide +kernel`) | four | four, one around the point of smallest slack found numerically | four, two of them around the two points of smallest slack found numerically |

The spot-check theorems are not used by the proofs. The counts of the C++ program are in the
files `cpp_verification.json` of the three certificate folders.

## Changes to the upstream library

`upstream_relax.patch` (14 files under `Zeta23/`) relaxes two constants in the general window
machinery: `b ≥ 1/2` becomes `b ≥ 1/8` (`LocalHypsCore`, `AdmFamily`, `FactsXi`) and `a ≥ 1/2`
becomes `a ≥ 1/4` (`WindowZeroSide`). The windows used here are not monotone and have to be scaled
by `2/5` to satisfy the total-variation bounds of the window class, which makes these two
normalised moments smaller. No statement of `Challenge.lean` or `Solution.lean` of the library
changes, and the patched library builds.

Nothing else is patched. Mathlib and the other dependencies are used unchanged, at the revisions
fixed in the library's `lake-manifest.json` (Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`), and
Lean is the version named in its `lean-toolchain`.

What the patch can and cannot affect:

- It changes five propositions that collect hypotheses (`LocalHypsCore`, `LocalHypsCoreW`,
  `AdmFamily`, `WindowZeroSide`, `FactsXi`), each of which now asks for less, and the proofs that
  used the old constants. It changes no definition of a mathematical object, and it adds no axiom
  and no `sorry`. Lean checks every proof of the patched library again, so a wrong change would
  make the build fail; it cannot make a false statement pass.
- The statements proved here are in the five `Challenge*.lean` files, which import only Mathlib.
  None of the patched files is among their imports, so the patch cannot change what is claimed.
- The library's own final theorems (`Solution.lean`, with the unchanged `Challenge.lean`) were
  built with the patch applied, in the working tree on 2 October 2026.

The patch is under the licence of the library, like the rest of this directory; see "Licence"
below.

## Build

```
git clone https://github.com/anthropics/formal-math && cd formal-math/zeta23
git checkout fbdc36bbf17d20af3fd0447c6d1a8a02773c9844
patch -p1 < /path/to/upstream_relax.patch
cp -r /path/to/{Distinct839,Simple673,Ceilings,Further,Line889,scripts} /path/to/*.lean .
cat /path/to/lakefile.additions.toml >> lakefile.toml
lake exe cache get
export LEAN_NUM_THREADS=4
lake build Distinct839.Local.RunAll
lake build Simple673.Local.RunAll
lake build Line889.Local.RunAll
lake build Solution839 Solution673 SolutionFurther Solution889 Ceilings SolutionCeilings
lake build Challenge839 Challenge673 ChallengeFurther Challenge889 ChallengeCeilings
```

`/path/to` is this directory. The three modules `Local.RunAll` are the compiled runs. The first
and the third need about 7 GB and one core each. The second needs about 11 GB, and it examines
its 96 parts on 96 threads of its own, whatever the value of `LEAN_NUM_THREADS`, so that it uses
every processor of the machine. The three are built first and one at a time so that they do not
run side by side. With more memory the three lines can be left out and `LEAN_NUM_THREADS` raised.

`lakefile.additions.toml` declares the libraries `Distinct839Checker`, `Simple673Checker` and
`Line889Checker` with
`precompileModules = true`, so that the three files `Local/Checker.lean` are compiled to native code
and loaded when the files `RunAll.lean` are checked. Times on a 12-core machine with 23 GB of
memory: `Distinct839.Local.RunAll` 33 to 65 minutes on one core; `Simple673.Local.RunAll` 33
minutes on the twelve cores and 11 GB (96 minutes when seven of the cores were in use by another
job); `Line889.Local.RunAll` 94 to 110 minutes and 7 GB; the rest of the library
and all other modules 9 to 13 minutes with the compiled Mathlib. The three modules
`Local.SpotChecks` are not built by the commands above; each needs 10 to 12 GB (build them one at
a time: `lake build Distinct839.Local.SpotChecks`, then `lake build Simple673.Local.SpotChecks`,
then `lake build Line889.Local.SpotChecks`).
To print the axioms: `lake env lean scripts/PrintAxioms839.lean`, `PrintAxioms673.lean`,
`PrintAxiomsFurther.lean`, `PrintAxioms889.lean`, `PrintAxiomsCeilings.lean`. The scripts for
`839`, `673` and `889` also list the spot-check theorems and import the `SpotChecks` modules, so
these three modules have to be built before the scripts are run.

To check that the Solution files prove exactly the statements of the Challenge files:
`python3 scripts/make_compare.py` writes `scripts/Compare839.lean`, `Compare673.lean`,
`CompareFurther.lean`, `Compare889.lean` and `CompareCeilings.lean` (the text of each Challenge file in a namespace, with every `sorry` replaced
by the Solution theorem of the same name), and `lake env lean scripts/Compare839.lean` etc. must
compile. The generated files are included.

The library in the working tree is the upstream commit named above with `upstream_relax.patch`
applied and nothing else: applying the patch to a checkout of that commit gives a `Zeta23/`
directory identical to the one used, and `ChallengeDeps.lean` is unchanged.

The files of this directory are those of the working tree, and everything in it was built there:
the compiled runs of the first and third search on 5 October 2026 (`Distinct839.Local.RunAll`
2433 s, `Line889.Local.RunAll` 6214 s) with their `SpotChecks` modules, the compiled run of the
second search on 6 October 2026 (`Simple673.Local.RunAll` 1973 s), and on that day every module
that depends on the second development, its `SpotChecks` module, the five axiom scripts and the
five comparison files. `axioms.txt` is the output of the scripts in that tree on 6 October 2026.

## Licence

The files in this directory are under the Apache License, Version 2.0 (`LICENSE`), Copyright 2026
Kristian Muri Knausgård. This is the licence of the library `zeta23` (Copyright 2026 Anthropic,
PBC), which is not included here, and from which three kinds of material in this directory are
derived: the patch `upstream_relax.patch`; the definitions that the statement files repeat from
the library; and lines of proofs that follow proofs of the library. `NOTICE` lists them and
reproduces the library's own notice file. The other directories of the repository are under the
MIT licence (`../LICENSE`).
