/-
Distinct839/Defs.lean — definitions and frozen data for the 83.9005% distinct-zero bound.

The window is `f(u) = 1 + ∑_{j=1}^{6} a_j cos(2π j u)` on `[-1/2, 1/2]` (zero outside), its Fourier
transform is the kernel `K`. The integer tables below are the frozen certificate data of the paper
(file `certificate/inputs.json` of the accompanying files, all entries are multiples of `10⁻⁶`).
This file contains definitions only.
-/
import Mathlib

open scoped BigOperators
open Real

noncomputable section

namespace Distinct839

/-! ## Window and kernel -/

/-- Window coefficients `10⁶ · a_j`, `j = 1, …, 6` (index `j - 1`). -/
def aInt : Fin 6 → ℤ := ![193305, -23105, 29166, 13952, -21009, 41052]

/-- The window coefficient `a_{j+1}` as a real number. -/
def aC (j : Fin 6) : ℝ := (aInt j : ℝ) / 1000000

/-- The cosine polynomial `1 + ∑ a_j cos(2π j u)`, without cutoff. -/
def fCos (u : ℝ) : ℝ := 1 + ∑ j : Fin 6, aC j * Real.cos (2 * π * ((j : ℕ) + 1) * u)

/-- The window `f(u) = 1 + ∑ a_j cos(2π j u)` on `|u| ≤ 1/2`, zero outside. -/
def fWin (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then fCos u else 0

/-- The profile used on the zeta side: `v = (2/5) · fCos`. The factor `2/5` makes the
total-variation hypotheses of the upstream window class hold; the kernel does not depend on it. -/
def vProf (s : ℝ) : ℝ := 2 / 5 * fCos s

/-- Normalised sinc: `sin(π t)/(π t)`, with value `1` at `0`. -/
def sincN (t : ℝ) : ℝ := Real.sinc (π * t)

/-- The kernel `K = f̂`: `K(t) = sinc(t) + ∑ a_j (sinc(t - j) + sinc(t + j))/2`. -/
def K (t : ℝ) : ℝ :=
  sincN t + ∑ j : Fin 6, aC j / 2 * (sincN (t - ((j : ℕ) + 1)) + sincN (t + ((j : ℕ) + 1)))

/-! ## Certificate parameters (exact rationals) -/

/-- separation threshold `d = 17/20` -/
def sep : ℝ := 17 / 20
/-- clipping level `c = 67/20` -/
def clipC : ℝ := 67 / 20
/-- pressure `α = 6219 · 10⁻⁶` -/
def alphaP : ℝ := 6219 / 1000000
/-- simple-site reward `x = 54350 · 10⁻⁶` -/
def rewX : ℝ := 54350 / 1000000
/-- double-site reward `y = 69433 · 10⁻⁶` -/
def rewY : ℝ := 69433 / 1000000
/-- span cost `b = 6 α` -/
def spanB : ℝ := 6 * alphaP
/-- bound for the oscillation of the telescoping state function -/
def omegaB : ℝ := 15882 / 1000000
/-- upper bound `C₀` for the energy constant `C(f)` -/
def energyC0 : ℝ := 266541 / 200000
/-- the final constant `q = 1645064/1960733` -/
def qFinal : ℝ := 1645064 / 1960733

/-- lower bound `β` for `K(t)²` on `|t| ≤ 17/20` -/
def betaC : ℝ := 8824337 / 134217728
/-- majorant amplitude `γ = 607/1000` -/
def gammaM : ℝ := 607 / 1000

/-- The clipped square `φ_c(t) = t² - (t - c)₊²`. -/
def phiC (c t : ℝ) : ℝ := t ^ 2 - (max (t - c) 0) ^ 2

/-- Multiplicity of a label: label `0` is a simple zero, label `1` a double zero. -/
def mulOf (a : Fin 2) : ℝ := (a : ℕ) + 1

/-- Site reward of a label: `x` for a simple zero, `y` for a double zero. -/
def rew (a : Fin 2) : ℝ := if a = 0 then rewX else rewY

/-- The two-sinc majorant `g(u) = γ (sinc(d(u - 1/2)) + sinc(d(u + 1/2)))²`, `d = 17/20`. -/
def gMaj (u : ℝ) : ℝ := gammaM * (sincN (sep * (u - 1 / 2)) + sincN (sep * (u + 1 / 2))) ^ 2

/-- `L = ∫ g = (2γ/d)(1 + sinc d)`. -/
def LMaj : ℝ := 2 * gammaM / sep * (1 + sincN sep)

/-- grid of the kernel table: cells `[k/H, (k+1)/H]`, `H = 16384` -/
def gridH : ℕ := 16384
/-- value scale of the kernel table, `V = 2²⁸` -/
def scaleV : ℕ := 268435456
/-- last cell index of the kernel table -/
def tabR : ℕ := 209009

/-! ## Frozen integer tables (units of `10⁻⁶`)

Labels: `0` = multiplicity one, `1` = multiplicity two. Pair type of labels `(a, b)` is `a + b`:
`0` = (1,1), `1` = (1,2), `2` = (2,2). -/

/-- pair type of two labels -/
def pairTy (a b : Fin 2) : Fin 3 := ⟨a.val + b.val, by omega⟩

/-- Pair weights `10⁶ · W^{ty}_{ij}` for `i < j` (entries with `i ≥ j` are `0`). -/
def Wtab : Fin 3 → Fin 7 → Fin 7 → ℤ := ![
    ![![0, 290164, 632845, 903375, 0, 1000000, 2000000],
      ![0, 0, 415442, 238229, 96624, 2000000, 1000000],
      ![0, 0, 0, 294392, 257850, 96624, 0],
      ![0, 0, 0, 0, 294392, 238229, 903375],
      ![0, 0, 0, 0, 0, 415442, 632845],
      ![0, 0, 0, 0, 0, 0, 290164],
      ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 613773, 943091, 1903375, 853682, 2000000, 4000000],
      ![0, 0, 686130, 639391, 96624, 2292634, 2000000],
      ![0, 0, 0, 700096, 835035, 96624, 853682],
      ![0, 0, 0, 0, 700096, 639391, 1903375],
      ![0, 0, 0, 0, 0, 686130, 943091],
      ![0, 0, 0, 0, 0, 0, 613773],
      ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 937383, 1344283, 3816137, 1707365, 4000000, 8000000],
      ![0, 0, 1865613, 1597288, 183862, 4585268, 4000000],
      ![0, 0, 0, 1197003, 2116857, 183862, 1707365],
      ![0, 0, 0, 0, 1197003, 1597288, 3816137],
      ![0, 0, 0, 0, 0, 1865613, 1344283],
      ![0, 0, 0, 0, 0, 0, 937383],
      ![0, 0, 0, 0, 0, 0, 0]]]

/-- Site rewards `10⁶ · h_{i,label}`. -/
def hTab : Fin 2 → Fin 7 → ℤ := ![
    ![0, 27175, 0, 0, 0, 27175, 0],
    ![2063, 30080, 2054, 1039, 2054, 30080, 2063]]

/-- Knot values `10⁶ · B_r^{ty}(3/4 + k/8)`, `k = 0, …, 13`, of the piecewise linear potentials
(position `r`, pair type `ty`). The first and last knot values are `0`. -/
def knotTab : Fin 6 → Fin 3 → Fin 14 → ℤ := ![
    ![![0, 0, 186, 976, 0, 0, 0, 0, -1914, -1005, 0, 0, 0, 0],
      ![0, 0, 334, 1483, 0, 0, 0, 0, 0, -920, -264, 0, 0, 0],
      ![0, 0, 2026, 2124, 0, 0, 0, 0, 0, -432, 0, 0, 0, 0]],
    ![![0, 0, -736, -177, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0],
      ![0, 0, 0, -495, 0, 0, 0, 0, 0, 524, 111, 0, 0, 0],
      ![0, 0, -924, -11, 0, 0, 0, 0, 0, 0, 773, 0, 0, 0]],
    ![![0, 0, 550, -799, 0, 0, 0, 0, 1790, 1005, 0, 0, 0, 0],
      ![0, 0, -334, -988, 0, 0, 0, 0, 0, 396, 153, 0, 0, 0],
      ![0, 0, -1102, -2113, 0, 0, 0, 0, 0, 432, -773, 0, 0, 0]],
    ![![0, 0, 550, -799, 0, 0, 0, 0, 1790, 1005, 0, 0, 0, 0],
      ![0, 0, -334, -988, 0, 0, 0, 0, 0, 396, 153, 0, 0, 0],
      ![0, 0, -1102, -2113, 0, 0, 0, 0, 0, 432, -773, 0, 0, 0]],
    ![![0, 0, -736, -177, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0],
      ![0, 0, 0, -495, 0, 0, 0, 0, 0, 524, 111, 0, 0, 0],
      ![0, 0, -924, -11, 0, 0, 0, 0, 0, 0, 773, 0, 0, 0]],
    ![![0, 0, 186, 976, 0, 0, 0, 0, -1914, -1005, 0, 0, 0, 0],
      ![0, 0, 334, 1483, 0, 0, 0, 0, 0, -920, -264, 0, 0, 0],
      ![0, 0, 2026, 2124, 0, 0, 0, 0, 0, -432, 0, 0, 0, 0]]]

/-- Hat function `max(0, 1 - |s|)`. -/
def hat (s : ℝ) : ℝ := max 0 (1 - |s|)

/-- The potential `B_r^{ty}`: piecewise linear with knots `3/4 + k/8`, zero outside `[3/4, 19/8]`. -/
def Bpot (r : Fin 6) (ty : Fin 3) (t : ℝ) : ℝ :=
  ∑ k : Fin 14, (knotTab r ty k : ℝ) / 1000000 * hat (8 * (t - (3 / 4 + (k : ℕ) / 8)))

/-- Position of the `i`-th point of a seven-point window with gaps `g`: `∑_{r < i} g_r`. -/
def pos (g : Fin 6 → ℝ) (i : Fin 7) : ℝ := ∑ r : Fin 6, if r.val < i.val then g r else 0

/-- The statement of the computer-assisted local inequality (the local inequality of the paper):
for all gaps `≥ 17/20` and all `2⁷` labelings,
`∑ h_{i,d_i} ≤ α ∑ g_r + ∑_{i<j} W_{ij}^{d_i d_j} K(y_j - y_i)² + ∑_r B_r^{d_r d_{r+1}}(g_r)`. -/
def LocalInequality : Prop :=
  ∀ (g : Fin 6 → ℝ) (lab : Fin 7 → Fin 2), (∀ r, sep ≤ g r) →
    ∑ i : Fin 7, (hTab (lab i) i : ℝ) / 1000000 ≤
      alphaP * ∑ r : Fin 6, g r
      + ∑ i : Fin 7, ∑ j : Fin 7,
          (if i < j then (Wtab (pairTy (lab i) (lab j)) i j : ℝ) / 1000000
              * K (pos g j - pos g i) ^ 2 else 0)
      + ∑ r : Fin 6, Bpot r (pairTy (lab r.castSucc) (lab r.succ)) (g r)

end Distinct839
