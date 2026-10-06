/-
Line889/Defs.lean — definitions and frozen data for the bound "more than 88.93% of the zeros of
the Riemann zeta function are simple or on the critical line".

The method is that of `Simple673` (clipping level `c = 2`: only the simple zeros on the line are
kept in the Gram part, so there is one kind of point and the certificate data carry no labels),
with a third window and with the count of `Further/Dist`: the zeros outside the Gram part enter
through the threshold inequality with a second level `t = 27/8 ≥ c` (`Further/Threshold.lean`).
The window is again `f(u) = 1 + ∑_{j=1}^{6} a_j cos(2π j u)` on `[-1/2, 1/2]`, with new
coefficients, and `K` is its Fourier transform. The integer tables are the frozen data of the
certificate for this count (`certificate_third/inputs.json` of the accompanying files; entries
in units of `10⁻⁶`; that file has the general format with labels and repeats each table once per
label or pair type, and the copies are identical).

Definitions that do not depend on the constants are those of `Distinct839/Defs.lean`
(`sincN`, `phiC`, `hat`, `pos`); they are exported into this namespace, so the lemmas proved
about them in `Distinct839` apply. This file contains definitions only.
-/
import Distinct839.Defs

open scoped BigOperators
open Real

noncomputable section

namespace Line889

export Distinct839 (sincN phiC hat pos)

/-! ## Window and kernel -/

/-- Window coefficients `10⁶ · a_j`, `j = 1, …, 6` (index `j - 1`). -/
def aInt : Fin 6 → ℤ := ![200566, 19, -9358, 9283, -6746, 8170]

/-- The window coefficient `a_{j+1}` as a real number. -/
def aC (j : Fin 6) : ℝ := (aInt j : ℝ) / 1000000

/-- The cosine polynomial `1 + ∑ a_j cos(2π j u)`, without cutoff. -/
def fCos (u : ℝ) : ℝ := 1 + ∑ j : Fin 6, aC j * Real.cos (2 * π * ((j : ℕ) + 1) * u)

/-- The window `f(u) = 1 + ∑ a_j cos(2π j u)` on `|u| ≤ 1/2`, zero outside. -/
def fWin (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then fCos u else 0

/-- The profile used on the zeta side: `v = (2/5) · fCos`, as in `Distinct839` and `Simple673`.
The factor makes `0 ≤ v ≤ 1` and the total-variation hypotheses of the upstream window class
hold, and keeps the normalised moments above the bounds `a ≥ 1/4`, `b ≥ 1/8` of the patched
library; the kernel does not depend on it. -/
def vProf (s : ℝ) : ℝ := 2 / 5 * fCos s

/-- The kernel `K = f̂`: `K(t) = sinc(t) + ∑ a_j (sinc(t - j) + sinc(t + j))/2`. -/
def K (t : ℝ) : ℝ :=
  sincN t + ∑ j : Fin 6, aC j / 2 * (sincN (t - ((j : ℕ) + 1)) + sincN (t + ((j : ℕ) + 1)))

/-! ## Certificate parameters (exact rationals) -/

/-- separation threshold `θ = 17/20` -/
def sep : ℝ := 17 / 20
/-- clipping level `c = 2` -/
def clipC : ℝ := 2
/-- the second level `t = 27/8 ≥ c` of the threshold inequality with two levels; it acts on the
zeros outside the Gram part -/
def tLev : ℝ := 27 / 8
/-- pressure `α = 6212 · 10⁻⁶` -/
def alphaP : ℝ := 6212 / 1000000
/-- site reward `x = 54525 · 10⁻⁶` -/
def rewX : ℝ := 54525 / 1000000
/-- span cost `b = 6 α` -/
def spanB : ℝ := 6 * alphaP
/-- bound `Ω = 75420 · 10⁻⁶` for the oscillation of the telescoping state function: the sum over
`q = 0, …, 4` of the ranges of the partial sums `∑_{r ≤ q} B_r` -/
def omegaB : ℝ := 75420 / 1000000
/-- upper bound `C₀` for the energy constant `C(f)` -/
def energyC0 : ℝ := 6662319 / 5000000
/-- `e₀ = 2t − t²/4 = 999/256`: the value, per unit of multiplicity, of a zero off the line of
multiplicity at least two. (A zero that is simple or on the line is worth `1 + x`.) -/
def e0C : ℝ := 2 * tLev - tLev ^ 2 / 4
/-- the final constant `(e₀ − C₀ − b)/(e₀ − 1 − x) = 50652159/56956375` -/
def qFinal : ℝ := 50652159 / 56956375

/-- lower bound `β = 3/50` for `K(t)²` on `|t| ≤ 17/20`. (The minimum of the kernel table over
these cells is `4483379 / 2²⁶ = 0.06680…`; the proof needs only `x ≤ β`.) -/
def betaC : ℝ := 3 / 50
/-- majorant amplitude `γ₀ = 61/100` -/
def gammaM : ℝ := 61 / 100
/-- bound `17/10` for the Gram matrix of the realised window on `θ`-separated sets. It lies
between `L = ∫ g = 1.6793…` and the clipping level `2`. -/
def normS : ℝ := 17 / 10

/-- The two-sinc majorant `g(u) = γ₀ (sinc(θ(u - 1/2)) + sinc(θ(u + 1/2)))²`, `θ = 17/20`. -/
def gMaj (u : ℝ) : ℝ := gammaM * (sincN (sep * (u - 1 / 2)) + sincN (sep * (u + 1 / 2))) ^ 2

/-- `L = ∫ g = (2γ₀/θ)(1 + sinc θ)`. -/
def LMaj : ℝ := 2 * gammaM / sep * (1 + sincN sep)

/-- grid of the kernel table: cells `[k/H, (k+1)/H]`, `H = 16384` -/
def gridH : ℕ := 16384
/-- value scale of the kernel table, `V = 2²⁸` -/
def scaleV : ℕ := 268435456
/-- last cell index of the kernel table; the table has `tabR + 1 = 262144 = 16 · 16384` entries -/
def tabR : ℕ := 262143

/-! ## Frozen integer tables (units of `10⁻⁶`) -/

/-- Pair weights `10⁶ · W_{ij}` for `i < j` (entries with `i ≥ j` are `0`). -/
def Wtab : Fin 7 → Fin 7 → ℤ := ![
    ![0, 263857, 364846, 468163, 608100, 1000000, 2000000],
    ![0, 0, 341543, 412303, 531836, 783798, 1000000],
    ![0, 0, 0, 394599, 445700, 531836, 608100],
    ![0, 0, 0, 0, 394599, 412303, 468163],
    ![0, 0, 0, 0, 0, 341543, 364846],
    ![0, 0, 0, 0, 0, 0, 263857],
    ![0, 0, 0, 0, 0, 0, 0]]

/-- Site rewards `10⁶ · κ_i`: the middle point of a frame receives `x`. -/
def hTab : Fin 7 → ℤ := ![0, 0, 0, 54525, 0, 0, 0]

/-- Knot values `10⁶ · B_r(3/4 + k/8)`, `k = 0, …, 13`, of the piecewise linear potentials
(position `r`). The first and last knot values are `0`, and each column sums to `0`. -/
def knotTab : Fin 6 → Fin 14 → ℤ := ![
    ![0, 1642, 6659, 7184, 14319, 19098, 0, 565, 4132, 4638, 5687, 0, 0, 0],
    ![0, -224, 4991, 4781, 1750, -3030, -2543, 15503, 5442, 5326, 5013, 16033, 16068, 0],
    ![0, -1418, -11650, -11965, -16069, -16068, 2543, -16068, -9574, -9964, -10700, -16033,
      -16068, 0],
    ![0, -1418, -11650, -11965, -16069, -16068, 2543, -16068, -9574, -9964, -10700, -16033,
      -16068, 0],
    ![0, -224, 4991, 4781, 1750, -3030, -2543, 15503, 5442, 5326, 5013, 16033, 16068, 0],
    ![0, 1642, 6659, 7184, 14319, 19098, 0, 565, 4132, 4638, 5687, 0, 0, 0]]

/-- The potential `B_r`: piecewise linear with knots `3/4 + k/8`, zero outside `[3/4, 19/8]`. -/
def Bpot (r : Fin 6) (t : ℝ) : ℝ :=
  ∑ k : Fin 14, (knotTab r k : ℝ) / 1000000 * hat (8 * (t - (3 / 4 + (k : ℕ) / 8)))

/-- The statement of the computer-assisted local inequality: for seven points with gaps
`g_r ≥ 17/20`,
`∑ κ_i ≤ α ∑ g_r + ∑_{i<j} W_{ij} K(y_j - y_i)² + ∑_r B_r(g_r)`. -/
def LocalInequality : Prop :=
  ∀ (g : Fin 6 → ℝ), (∀ r, sep ≤ g r) →
    ∑ i : Fin 7, (hTab i : ℝ) / 1000000 ≤
      alphaP * ∑ r : Fin 6, g r
      + ∑ i : Fin 7, ∑ j : Fin 7,
          (if i < j then (Wtab i j : ℝ) / 1000000 * K (pos g j - pos g i) ^ 2 else 0)
      + ∑ r : Fin 6, Bpot r (g r)

end Line889
