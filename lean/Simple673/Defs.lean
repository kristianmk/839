/-
Simple673/Defs.lean — definitions and frozen data for the bound "more than 67.35% of the zeros
of the Riemann zeta function are simple and on the critical line".

The method is that of `Distinct839` with clipping level `c = 2`: only the simple zeros on the
line are kept in the Gram part, so there is one kind of point and the certificate data carry no
labels. The window is `f(u) = 1 + ∑_{j=1}^{10} a_j cos(2π j u)` on `[-1/2, 1/2]`, a cosine
polynomial with ten terms (the window of `Distinct839` has six), and `K` is its Fourier
transform. The local inequality is for frames of eight consecutive points, that is, for seven
gaps (the frames of `Distinct839` have seven points). The integer tables are the frozen
certificate data of `certificate_line/inputs.json` of the accompanying files (entries in units of
`10⁻⁶`; that file repeats each table for the three label types of the general format, the three
copies are identical).

Definitions that do not depend on the constants or on the number of points of a frame are those
of `Distinct839/Defs.lean` (`sincN`, `phiC`, `hat`); they are exported into this namespace, so the
lemmas proved about them in `Distinct839` apply. This file contains definitions only.
-/
import Distinct839.Defs

open scoped BigOperators
open Real

noncomputable section

namespace Simple673

export Distinct839 (sincN phiC hat)

/-! ## Window and kernel -/

/-- Window coefficients `10⁶ · a_j`, `j = 1, …, 10` (index `j - 1`). -/
def aInt : Fin 10 → ℤ := ![122290, -45012, 16241, 1887, 2711, 3731, -5307, 2982, -5153, 5358]

/-- The window coefficient `a_{j+1}` as a real number. -/
def aC (j : Fin 10) : ℝ := (aInt j : ℝ) / 1000000

/-- The cosine polynomial `1 + ∑ a_j cos(2π j u)`, without cutoff. -/
def fCos (u : ℝ) : ℝ := 1 + ∑ j : Fin 10, aC j * Real.cos (2 * π * ((j : ℕ) + 1) * u)

/-- The window `f(u) = 1 + ∑ a_j cos(2π j u)` on `|u| ≤ 1/2`, zero outside. -/
def fWin (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then fCos u else 0

/-- The profile used on the zeta side: `v = (2/5) · fCos`, as in `Distinct839`. The factor makes
`0 ≤ v ≤ 1` and the total-variation hypotheses of the upstream window class hold, and keeps the
normalised moments above the bounds `a ≥ 1/4`, `b ≥ 1/8` of the patched library; the kernel does
not depend on it. -/
def vProf (s : ℝ) : ℝ := 2 / 5 * fCos s

/-- The kernel `K = f̂`: `K(t) = sinc(t) + ∑ a_j (sinc(t - j) + sinc(t + j))/2`. -/
def K (t : ℝ) : ℝ :=
  sincN t + ∑ j : Fin 10, aC j / 2 * (sincN (t - ((j : ℕ) + 1)) + sincN (t + ((j : ℕ) + 1)))

/-! ## Certificate parameters (exact rationals) -/

/-- separation threshold `θ = 17/20` -/
def sep : ℝ := 17 / 20
/-- clipping level `c = 2` -/
def clipC : ℝ := 2
/-- pressure `α = 627 · 10⁻⁶` -/
def alphaP : ℝ := 627 / 1000000
/-- site reward `x₁ = 8722 · 10⁻⁶` -/
def rewX : ℝ := 8722 / 1000000
/-- span cost `b = 7 α`: each gap of a chain lies in at most seven frames -/
def spanB : ℝ := 7 * alphaP
/-- bound `Ω = 3882 · 10⁻⁶` for the oscillation of the telescoping state function: the sum over
`q = 0, …, 5` of the ranges of the partial sums `∑_{r ≤ q} B_r` -/
def omegaB : ℝ := 3882 / 1000000
/-- upper bound `C₀` for the energy constant `C(f)` -/
def energyC0 : ℝ := 6639737 / 5000000
/-- the final constant `(2 − C₀ − b)/(1 − x₁) = 1669159/2478195` -/
def qFinal : ℝ := 1669159 / 2478195

/-- lower bound `β = 1/20` for `K(t)²` on `|t| ≤ 17/20`. (The minimum of the kernel table over
these cells is `13707941 / 2²⁸ = 0.05106…`; the proof needs only `x₁ ≤ β`.) -/
def betaC : ℝ := 1 / 20
/-- majorant amplitude `γ₀ = 13/20` -/
def gammaM : ℝ := 13 / 20
/-- bound `19/10` for the Gram matrix of the realised window on `θ`-separated sets. It lies
between `L = ∫ g = 1.7894…` and the clipping level `2`. -/
def normS : ℝ := 19 / 10

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
def Wtab : Fin 8 → Fin 8 → ℤ := ![
    ![0, 159939, 0, 280438, 143766, 709387, 1000000, 2000000],
    ![0, 0, 264496, 385569, 340591, 856233, 581225, 1000000],
    ![0, 0, 0, 389188, 614430, 757940, 856233, 709387],
    ![0, 0, 0, 0, 372750, 614430, 340591, 143766],
    ![0, 0, 0, 0, 0, 389188, 385569, 280438],
    ![0, 0, 0, 0, 0, 0, 264496, 0],
    ![0, 0, 0, 0, 0, 0, 0, 159939],
    ![0, 0, 0, 0, 0, 0, 0, 0]]

/-- Site rewards `10⁶ · κ_i`: one point of a frame (the fourth, index `3`) receives `x₁`. -/
def hTab : Fin 8 → ℤ := ![0, 0, 0, 8722, 0, 0, 0, 0]

/-- Knot values `10⁶ · B_r(3/4 + k/8)`, `k = 0, …, 13`, of the piecewise linear potentials
(position `r`). The first and last knot values are `0`, and each column sums to `0`. -/
def knotTab : Fin 7 → Fin 14 → ℤ := ![
    ![0, 647, 555, 518, 647, 647, 647, 0, 0, 270, 325, 0, 647, 0],
    ![0, 0, 91, 45, 0, 0, 0, 0, 0, 86, 58, 0, 0, 0],
    ![0, -425, -425, -342, -425, -425, -425, 221, 221, -275, -244, -425, -425, 0],
    ![0, -444, -442, -442, -444, -444, -444, -442, -442, -162, -278, 850, -444, 0],
    ![0, -425, -425, -342, -425, -425, -425, 221, 221, -275, -244, -425, -425, 0],
    ![0, 0, 91, 45, 0, 0, 0, 0, 0, 86, 58, 0, 0, 0],
    ![0, 647, 555, 518, 647, 647, 647, 0, 0, 270, 325, 0, 647, 0]]

/-- The potential `B_r`: piecewise linear with knots `3/4 + k/8`, zero outside `[3/4, 19/8]`. -/
def Bpot (r : Fin 7) (t : ℝ) : ℝ :=
  ∑ k : Fin 14, (knotTab r k : ℝ) / 1000000 * hat (8 * (t - (3 / 4 + (k : ℕ) / 8)))

/-- Position of the point `i` of a frame with gaps `g`: the sum of the first `i` gaps. -/
def pos (g : Fin 7 → ℝ) (i : Fin 8) : ℝ := ∑ r : Fin 7, if r.val < i.val then g r else 0

/-- The statement of the computer-assisted local inequality: for eight points with gaps
`g_r ≥ 17/20`,
`∑ κ_i ≤ α ∑ g_r + ∑_{i<j} W_{ij} K(y_j - y_i)² + ∑_r B_r(g_r)`. -/
def LocalInequality : Prop :=
  ∀ (g : Fin 7 → ℝ), (∀ r, sep ≤ g r) →
    ∑ i : Fin 8, (hTab i : ℝ) / 1000000 ≤
      alphaP * ∑ r : Fin 7, g r
      + ∑ i : Fin 8, ∑ j : Fin 8,
          (if i < j then (Wtab i j : ℝ) / 1000000 * K (pos g j - pos g i) ^ 2 else 0)
      + ∑ r : Fin 7, Bpot r (g r)

end Simple673
