/-
Line889/Kernel/Compute.lean — the kernel table of the third window as an exact rational
computation.

This file contains definitions only; their soundness is proved in `Line889/Kernel/Sound.lean`.
It is a line-by-line port of the reference program `build_kernel.py`, with exact arithmetic in
`ℚ`. The part of the computation that does not depend on the window is that of
`Distinct839/Kernel/Compute.lean` and is used unchanged:

* `Distinct839.Kernel.piLo < π < Distinct839.Kernel.piHi` are the twenty-digit bounds of Mathlib
  (`Real.pi_gt_d20`, `Real.pi_lt_d20`). The Python program uses forty-digit Machin bounds; the
  resulting tables are identical.
* For `j < H/2`, `H = 16384`, and `r = (2j+1)/(2H)`, the record `Distinct839.Kernel.trigEncl j`
  encloses `sin(π r)/π` and `cos(π r)` by Taylor polynomials with 10 and 11 terms evaluated at
  `piLo·r` and `piHi·r`, divided by `piHi` or `piLo`, and rounded outwards to multiples of `2⁻⁷⁰`.

The part that depends on the window coefficients `aInt` is defined here:

* For the cell `k` with midpoint `t = (2k+1)/(2H)`, `cellVal` evaluates
  `Q(t) = 1/t + ∑ (-1)^j a_j t/(t² - j²)` and `Q'(t)`, encloses `K(t) = sin(π t)/π · Q(t)` and
  `K'(t) = cos(π t) Q(t) + sin(π t)/π · Q'(t)`, and returns
  `⌊V · [ℓ - (1/(2H)) · min(π, D + π²/(2H))]₊²⌋`, `V = 2²⁸`, with `ℓ ≤ |K(t)|`, `D ≥ |K'(t)|` and
  `π` replaced by `piHi`.
* `kTab k` reduces `k` modulo `H` and reflects the second half of each period onto the first
  (`sin(π t)` and `cos(π t)` are determined, up to a common sign, by `t mod 1`).

The table is used for the cells `k = 0, …, 262143` (16 periods, 262144 entries); the array of
these entries is `kTabArray` in `Line889/Kernel/Array.lean`.

This file and `Line889/Kernel/Array.lean` are, with `Line889/Defs.lean` and the checker, all that
the compiled run of the local inequality imports from the development; the proofs about the
kernel are in the other files of this directory.
-/
import Distinct839.Kernel.Compute
import Line889.Defs

open scoped BigOperators

namespace Line889.Kernel

/-! ## The rational factor of the kernel -/

/-- `Q(t) = 1/t + ∑_{j=1}^{6} (-1)^j a_j t/(t² - j²)` in `ℚ`. -/
def ratQ (t : ℚ) : ℚ :=
  1 / t + ∑ j : Fin 6,
    (-1) ^ ((j : ℕ) + 1) * ((aInt j : ℚ) / 1000000) * t / (t ^ 2 - ((j : ℕ) + 1) ^ 2)

/-- `Q'(t) = -1/t² - ∑_{j=1}^{6} (-1)^j a_j (t² + j²)/(t² - j²)²` in `ℚ`. -/
def derQ (t : ℚ) : ℚ :=
  -1 / t ^ 2 - ∑ j : Fin 6,
    (-1) ^ ((j : ℕ) + 1) * ((aInt j : ℚ) / 1000000) * (t ^ 2 + ((j : ℕ) + 1) ^ 2)
      / (t ^ 2 - ((j : ℕ) + 1) ^ 2) ^ 2

/-! ## One table entry -/

/-- The lower bound `[ℓ - (1/(2H)) min(π, D + π²/(2H))]₊` for `|K|` on cell `k`, given an enclosure
`e` of `sin(π t)/π` and `cos(π t)` at the midpoint `t = (2k+1)/(2H)` up to a common sign. -/
def cellLow (e : Distinct839.Kernel.TrigEncl) (k : ℕ) : ℚ :=
  let t : ℚ := (2 * k + 1) / 32768
  let rat := ratQ t
  let der := derQ t
  -- `dl ≤ ±K'(t) ≤ du`
  let dl := min (rat * e.cl) (rat * e.cu) + min (der * e.sl) (der * e.su)
  let du := max (rat * e.cl) (rat * e.cu) + max (der * e.sl) (der * e.su)
  -- `|K'| ≤ D + π²/(2H)` on the cell, and `|K'| ≤ π` everywhere
  let db := min Distinct839.Kernel.piHi
    (max |dl| |du| + Distinct839.Kernel.piHi * Distinct839.Kernel.piHi / 32768)
  max 0 (|rat| * e.sl - db / 32768)

/-- The table entry `⌊V · low²⌋` of cell `k`, `V = 2²⁸`. -/
def cellVal (e : Distinct839.Kernel.TrigEncl) (k : ℕ) : ℕ :=
  let low := cellLow e k
  ⌊low * low * 268435456⌋₊

/-- The table, with the trigonometric enclosures supplied by `T` (used to share them). -/
def kTabWith (T : ℕ → Distinct839.Kernel.TrigEncl) (k : ℕ) : ℕ :=
  let j := k % 16384
  if j < 8192 then cellVal (T j) k else cellVal (T (16383 - j)).reflect k

/-- **The kernel table**: `kTab k / 2²⁸ ≤ K(t)²` on the cell `[k/16384, (k+1)/16384]`
(`kTab_sound`). -/
def _root_.Line889.kTab (k : ℕ) : ℕ := kTabWith Distinct839.Kernel.trigEncl k

end Line889.Kernel
