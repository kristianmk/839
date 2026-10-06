/-
Distinct839/Gram/PhiC.lean — scalar facts about the clipped square `φ_c(t) = t² - (t - c)₊²`.

`φ_c` is the convex function of the threshold inequality: `φ_c(t) = t²` for `t ≤ c` and
`φ_c(t) = 2ct - c²` for `t ≥ c`. It differs from the upstream function `g_c` (`gc`, in
`Zeta23/ZeroSide/RankTraceMult.lean`) by the linear term `c t`. This file contains the relation
to `gc`, the tangent-line bound, and the two-point estimate used for the two-by-two blocks of
the Gram theorem.
-/
import Distinct839.Defs
import Zeta23.ZeroSide.RankTraceMult

open Zeta23.ZeroSide.RankTraceMult

namespace Distinct839.Gram

/-- `φ_c(t) = g_c(t) + c t`, where `g_c` is the upstream function `gc`. -/
lemma phiC_eq_gc_add (c t : ℝ) : phiC c t = gc c t + c * t := by
  unfold phiC gc; ring

/-- Below the clipping level `φ_c` is the square. -/
lemma phiC_of_le {c t : ℝ} (h : t ≤ c) : phiC c t = t ^ 2 := by
  unfold phiC; rw [max_eq_right (by linarith)]; ring

/-- Above the clipping level `φ_c` is affine. -/
lemma phiC_of_ge {c t : ℝ} (h : c ≤ t) : phiC c t = 2 * c * t - c ^ 2 := by
  unfold phiC; rw [max_eq_left (by linarith)]; ring

/-- `φ_c(0) = 0` for `c ≥ 0`. -/
lemma phiC_zero {c : ℝ} (hc : 0 ≤ c) : phiC c 0 = 0 := by
  rw [phiC_of_le hc]; ring

/-- Tangent-line bound (convexity of `φ_c`): for `t₀ ≤ c` the tangent of `t ↦ t²` at `t₀` lies
below `φ_c`. -/
lemma tangent_le_phiC {c t₀ t : ℝ} (h₀ : t₀ ≤ c) :
    t₀ ^ 2 + 2 * t₀ * (t - t₀) ≤ phiC c t := by
  rcases le_or_gt t c with h | h
  · rw [phiC_of_le h]; nlinarith [sq_nonneg (t - t₀)]
  · rw [phiC_of_ge h.le]; nlinarith [mul_nonneg (sub_nonneg.2 h₀) (sub_nonneg.2 h.le), sq_nonneg (c - t₀)]

/-- Sums of `φ_c` and of `g_c` over a finite family differ by `c` times the sum of the points. -/
lemma sum_phiC_eq {ι : Type*} (s : Finset ι) (c : ℝ) (μ : ι → ℝ) :
    ∑ i ∈ s, phiC c (μ i) = ∑ i ∈ s, gc c (μ i) + c * ∑ i ∈ s, μ i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => phiC_eq_gc_add c _

/-- **Two-point estimate.** Let `l₁, l₂` have the sum and the sum of squares of the eigenvalues
of the symmetric matrix `[[p, q], [q, r]]`. If `w ≤ q²` and the comparison matrix
`[[p, √w], [√w, r]]` has both eigenvalues at most `c` (that is `p, r ≤ c` and
`w ≤ (c - p)(c - r)`), then `φ_c(l₁) + φ_c(l₂) ≥ p² + r² + 2w`.

Proof: with `d₀ = √((p - r)² + 4w)` and `t± = (p + r ± d₀)/2` (the eigenvalues of the comparison
matrix), one of `l₁, l₂` is at least `t₊ ≤ c`; add the tangent-line bounds at `t₊` and `t₋`. -/
theorem phiC_pair_ge {c p r w l₁ l₂ : ℝ} (hsum : l₁ + l₂ = p + r)
    (hsq : ∃ q : ℝ, w ≤ q ^ 2 ∧ l₁ ^ 2 + l₂ ^ 2 = p ^ 2 + r ^ 2 + 2 * q ^ 2)
    (hw : 0 ≤ w) (hp : p ≤ c) (hr : r ≤ c) (hdet : w ≤ (c - p) * (c - r)) :
    p ^ 2 + r ^ 2 + 2 * w ≤ phiC c l₁ + phiC c l₂ := by
  obtain ⟨q, hwq, hsq⟩ := hsq
  have hD : 0 ≤ (p - r) ^ 2 + 4 * w := by positivity
  set d₀ := Real.sqrt ((p - r) ^ 2 + 4 * w) with hd₀
  have hd₀nn : 0 ≤ d₀ := Real.sqrt_nonneg _
  have hd₀sq : d₀ ^ 2 = (p - r) ^ 2 + 4 * w := Real.sq_sqrt hD
  -- the top eigenvalue of the comparison matrix is at most `c`
  have htop : (p + r + d₀) / 2 ≤ c := by
    have h1 : d₀ ≤ 2 * c - p - r := by
      apply Real.sqrt_le_iff.2
      refine ⟨by linarith, ?_⟩
      nlinarith
    linarith
  have hbot : (p + r - d₀) / 2 ≤ c := by linarith
  -- the difference of `l₁, l₂` is at least `d₀` in absolute value
  have hdiff : d₀ ^ 2 ≤ (l₁ - l₂) ^ 2 := by
    have : (l₁ - l₂) ^ 2 = 2 * (l₁ ^ 2 + l₂ ^ 2) - (l₁ + l₂) ^ 2 := by ring
    rw [this, hsq, hsum, hd₀sq]; nlinarith
  have habs : d₀ ≤ |l₁ - l₂| := by
    have := sq_le_sq.1 hdiff
    rwa [abs_of_nonneg hd₀nn] at this
  have hl₂ : l₂ = p + r - l₁ := by linarith
  have hw' : w = (d₀ ^ 2 - (p - r) ^ 2) / 4 := by linarith
  clear_value d₀
  subst hl₂ hw'
  rcases le_abs.1 habs with h | h
  · -- `l₁ - l₂ ≥ d₀`: tangent at the top point for `l₁`, at the bottom point for `l₂`
    have t1 := tangent_le_phiC (t := l₁) htop
    have t2 := tangent_le_phiC (t := p + r - l₁) hbot
    have := mul_nonneg hd₀nn (sub_nonneg.2 h)
    nlinarith
  · -- `l₂ - l₁ ≥ d₀`: the same with the roles exchanged
    have t1 := tangent_le_phiC (t := p + r - l₁) htop
    have t2 := tangent_le_phiC (t := l₁) hbot
    have := mul_nonneg hd₀nn (sub_nonneg.2 h)
    nlinarith

end Distinct839.Gram
