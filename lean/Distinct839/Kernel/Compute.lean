/-
Distinct839/Kernel/Compute.lean — the kernel table as an exact rational computation.

This file contains definitions only; their soundness is proved in `Distinct839/Kernel/Sound.lean`.
It is a line-by-line port of `certificate/build_kernel.py`, with exact arithmetic in `ℚ`:

* `piLo < π < piHi` are the twenty-digit bounds of Mathlib (`Real.pi_gt_d20`, `Real.pi_lt_d20`).
  The Python program uses forty-digit Machin bounds; the resulting tables are identical.
* For `j < H/2`, `H = 16384`, and `r = (2j+1)/(2H)`, the record `trigEncl j` encloses
  `sin(π r)/π` and `cos(π r)` by Taylor polynomials with 10 and 11 terms evaluated at `piLo·r` and
  `piHi·r`, divided by `piHi` or `piLo`, and rounded outwards to multiples of `2⁻⁷⁰`.
* For the cell `k` with midpoint `t = (2k+1)/(2H)`, `cellVal` evaluates
  `Q(t) = 1/t + ∑ (-1)^j a_j t/(t² - j²)` and `Q'(t)`, encloses `K(t) = sin(π t)/π · Q(t)` and
  `K'(t) = cos(π t) Q(t) + sin(π t)/π · Q'(t)`, and returns
  `⌊V · [ℓ - (1/(2H)) · min(π, D + π²/(2H))]₊²⌋`, `V = 2²⁸`, with `ℓ ≤ |K(t)|`, `D ≥ |K'(t)|` and
  `π` replaced by `piHi`.
* `kTab k` reduces `k` modulo `H` and reflects the second half of each period onto the first
  (`sin(π t)` and `cos(π t)` are determined, up to a common sign, by `t mod 1`).
-/
import Distinct839.Kernel.Taylor

open scoped BigOperators

namespace Distinct839.Kernel

/-! ## Rational constants -/

/-- Rational lower bound for `π` (Mathlib's `Real.pi_gt_d20`). -/
def piLo : ℚ := 314159265358979323846 / 10 ^ 20

/-- Rational upper bound for `π` (Mathlib's `Real.pi_lt_d20`). -/
def piHi : ℚ := 314159265358979323847 / 10 ^ 20

/-- Rounding down to a multiple of `2⁻⁷⁰`. -/
def dyLo (x : ℚ) : ℚ := (⌊x * 2 ^ 70⌋ : ℚ) / 2 ^ 70

/-- Rounding up (strictly) to a multiple of `2⁻⁷⁰`. -/
def dyHi (x : ℚ) : ℚ := ((⌊x * 2 ^ 70⌋ : ℚ) + 1) / 2 ^ 70

/-! ## Enclosures of `sin(π r)/π` and `cos(π r)` -/

/-- Four rational bounds: `sl ≤ sin(π r)/π ≤ su` and `cl ≤ cos(π r) ≤ cu` (or `-cos`, after
reflection). -/
structure TrigEncl where
  /-- lower bound for `sin(π r)/π` -/
  sl : ℚ
  /-- upper bound for `sin(π r)/π` -/
  su : ℚ
  /-- lower bound for the cosine -/
  cl : ℚ
  /-- upper bound for the cosine -/
  cu : ℚ
deriving Inhabited

/-- The enclosure at `r = (2j+1)/(2H)`, `H = 16384`, as in `build_kernel.py`. -/
def trigEncl (j : ℕ) : TrigEncl :=
  let r : ℚ := (2 * j + 1) / 32768
  let xl := piLo * r
  let xu := piHi * r
  { sl := dyLo (sinPoly 10 xl / piHi)
    su := dyHi (sinPoly 11 xu / piLo)
    cl := dyLo (cosPoly 10 xu)
    cu := dyHi (cosPoly 11 xl) }

/-- Reflection `r ↦ 1 - r`: the sine is unchanged, the cosine changes sign. -/
def TrigEncl.reflect (e : TrigEncl) : TrigEncl :=
  { sl := e.sl, su := e.su, cl := -e.cu, cu := -e.cl }

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
def cellLow (e : TrigEncl) (k : ℕ) : ℚ :=
  let t : ℚ := (2 * k + 1) / 32768
  let rat := ratQ t
  let der := derQ t
  -- `dl ≤ ±K'(t) ≤ du`
  let dl := min (rat * e.cl) (rat * e.cu) + min (der * e.sl) (der * e.su)
  let du := max (rat * e.cl) (rat * e.cu) + max (der * e.sl) (der * e.su)
  -- `|K'| ≤ D + π²/(2H)` on the cell, and `|K'| ≤ π` everywhere
  let db := min piHi (max |dl| |du| + piHi * piHi / 32768)
  max 0 (|rat| * e.sl - db / 32768)

/-- The table entry `⌊V · low²⌋` of cell `k`, `V = 2²⁸`. -/
def cellVal (e : TrigEncl) (k : ℕ) : ℕ :=
  let low := cellLow e k
  ⌊low * low * 268435456⌋₊

/-- The table, with the trigonometric enclosures supplied by `T` (used to share them). -/
def kTabWith (T : ℕ → TrigEncl) (k : ℕ) : ℕ :=
  let j := k % 16384
  if j < 8192 then cellVal (T j) k else cellVal (T (16383 - j)).reflect k

/-- **The kernel table**: `kTab k / 2²⁸ ≤ K(t)²` on the cell `[k/16384, (k+1)/16384]`
(`kTab_sound`). -/
def _root_.Distinct839.kTab (k : ℕ) : ℕ := kTabWith trigEncl k

end Distinct839.Kernel
