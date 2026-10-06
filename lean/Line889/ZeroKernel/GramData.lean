/-
Line889/ZeroKernel/GramData.lean — the Gram data of the realised window (`gramData`,
`gramDataLayer`).

For `1/2 ≤ λ < 1`, the window realising the profile `vProf` at height `T` (upstream
`Pfam lam T = (paramsOf stdProfile lam).atV vProf T`) satisfies, for all large `T`:

1. for two ordinates in the bulk `[T + √T, 2T - √T]`, the Gram entry is within
   `η(T) = 24/L + 8 Z c²/T → 0` of the kernel value `K(y - y')` (`Bulk.lean`);
2. on every `sep`-separated finite set of ordinates the Gram matrix is bounded by
   `(2/(5a)) · LMaj ≤ 17/10 = normS` (`Separated.lean`), because `a ≥ 2/5 - 2/L`
   (`Kernel.lean`) and `LMaj ≤ 1.68`: for `L ≥ 4000`, `a ≥ 0.3995` and
   `(2/(5 · 0.3995)) · 1.68 = 1.6821… < 1.7`.

The window class `AdmWindow` of the realised window, the integral formula for `K` and the
majorant statements are hypotheses, proved in other layers. `gramData` has them as explicit
hypotheses; `gramDataLayer` is the same theorem with the hypotheses written as the statements
`AdmAt`, `KIntegral`, … of `Spec.lean` and `Spec2.lean`.
-/
import Line889.ZeroKernel.Bulk
import Line889.ZeroKernel.Separated

open scoped BigOperators
open Real Filter Topology MeasureTheory Zeta23

noncomputable section

namespace Line889.ZeroKernel

/-- The error of part (1): `η(T) = 24/L + 8 Z c²/T`. -/
def etaGram (lam cW T : ℝ) : ℝ :=
  24 / (Pst lam).L T + 8 * Distinct839.ZeroKernel.zetaTwoZ * cW ^ 2 / T

lemma tendsto_etaGram {lam : ℝ} (h0 : 0 < lam) (cW : ℝ) :
    Tendsto (etaGram lam cW) atTop (𝓝 0) := by
  have hL : Tendsto (fun T => (Pst lam).L T) atTop atTop :=
    Zeta23.Assembly.tendsto_L_atTop (Pst lam) h0
  have h1 : Tendsto (fun T => 24 / (Pst lam).L T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have h2 : Tendsto (fun T : ℝ => 8 * Distinct839.ZeroKernel.zetaTwoZ * cW ^ 2 / T) atTop
      (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := h1.add h2
  rw [add_zero] at h
  exact h

/-- `LMaj ≥ 0`. -/
lemma LMaj_nonneg : 0 ≤ LMaj := by
  have h := (abs_le.mp (Distinct839.ZeroKernel.abs_sincN_le_one sep)).1
  unfold LMaj gammaM sep at *
  exact mul_nonneg (by norm_num) (by linarith)

/-- The constant of part (2) is below `normS = 17/10` once `a ≥ 0.3995`:
`(2/(5a)) · LMaj ≤ (2/(5 · 0.3995)) · 1.68 = 1.6821…`. -/
lemma sepConst_le {a : ℝ} (ha : 3995 / 10000 ≤ a) (hLM : LMajBound) :
    2 / (5 * a) * LMaj ≤ normS := by
  have ha0 : 0 < a := by linarith
  have hLM' : LMaj ≤ 168 / 100 := hLM
  calc 2 / (5 * a) * LMaj ≤ 2 / (5 * a) * (168 / 100) :=
        mul_le_mul_of_nonneg_left hLM' (by positivity)
    _ ≤ normS := by
        unfold normS
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        linarith

/-- For `L ≥ 4000` the normalisation is `a ≥ 0.3995`. -/
lemma av_ge_of_L {lam cW T : ℝ}
    (hK : ∀ t : ℝ, K t = ∫ u in (-(1:ℝ)/2)..(1/2), fCos u * Real.cos (2 * π * t * u))
    (hW : AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW) (hL : 4000 ≤ (Pst lam).L T) :
    3995 / 10000 ≤ AdmWindow.av (phiW lam T) ((Pst lam).L T) := by
  have h := av_lower hK hW
  have h2 : 2 / (Pst lam).L T ≤ 2 / 4000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  linarith

/-- The window class of the realised window at height `T`, from the hypothesis of `gramData`,
once `L ≥ 8`. -/
lemma admWindow_of {lam cW T : ℝ}
    (hAdm : ∀ T, 8 * (paramsOf stdProfile lam).w ≤ (paramsOf stdProfile lam).L T →
      AdmWindow ((paramsOf stdProfile lam).phiV vProf T) ((paramsOf stdProfile lam).L T)
        (paramsOf stdProfile lam).w cW)
    (hL : 8 ≤ (Pst lam).L T) :
    AdmWindow (phiW lam T) ((Pst lam).L T) 1 cW := by
  have hw : (paramsOf stdProfile lam).w = 1 := rfl
  have h8 : 8 * (paramsOf stdProfile lam).w ≤ (paramsOf stdProfile lam).L T := by
    rw [hw, mul_one]
    exact hL
  exact hAdm T h8

end Line889.ZeroKernel

namespace Line889

open Line889.ZeroKernel

/-- **Gram data of the realised window.** For `1/2 ≤ λ < 1`, given the window class of the
realised window (`hAdm`), the integral formula for `K` (`hK`) and the majorant statements
(`hMP`, `hLM`, `hSB`): (1) Gram entries of ordinates in the bulk `[T + √T, 2T - √T]` are within
`η(T) → 0` of the kernel values; (2) on `sep`-separated finite sets of ordinates the Gram matrix
is bounded by `normS = 17/10`, for all large `T`. -/
theorem gramData {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam < 1) {cW : ℝ}
    (hAdm : ∀ T, 8 * (paramsOf stdProfile lam).w ≤ (paramsOf stdProfile lam).L T →
      AdmWindow ((paramsOf stdProfile lam).phiV vProf T) ((paramsOf stdProfile lam).L T)
        (paramsOf stdProfile lam).w cW)
    (hK : ∀ t : ℝ, K t = ∫ u in (-(1:ℝ)/2)..(1/2), fCos u * Real.cos (2 * π * t * u))
    (hMP : MajorantPointwise) (hLM : LMajBound) (hSB : SeparatedBound) :
    GramDataStatement lam := by
  have h0 : 0 < lam := by linarith
  have h1 : lam ≤ 1 := hlam1.le
  have hevL : ∀ᶠ T in atTop, 4000 ≤ (Pst lam).L T :=
    (Zeta23.Assembly.tendsto_L_atTop (Pst lam) h0).eventually_ge_atTop 4000
  have hevT : ∀ᶠ T in atTop, (16 : ℝ) ≤ T := eventually_ge_atTop 16
  refine ⟨⟨etaGram lam cW, tendsto_etaGram h0 cW, ?_⟩, ?_⟩
  · filter_upwards [hevL, hevT] with T hL hT
    intro γ γ' hγ hγ2 hγ' hγ'2
    have hW := admWindow_of hAdm (T := T) (by linarith)
    exact abs_gramKappa_sub_K_le h0 h1 hK hW (by linarith) hT hγ hγ2 hγ' hγ'2
  · filter_upwards [hevL] with T hL
    intro ι _ γ x hsep
    have hW := admWindow_of hAdm (T := T) (by linarith)
    have ha := av_ge_of_L hK hW hL
    have hsum := sum_gramKappa_le h0 h1 hW (by linarith) hMP hSB ι γ x hsep
    refine hsum.trans ?_
    exact mul_le_mul_of_nonneg_right (sepConst_le ha hLM)
      (Finset.sum_nonneg fun i _ => sq_nonneg (x i))

/-- **Layer `ZeroKernel`.** The Gram data of the realised window, with the hypotheses in the form
of the interface: admissibility `AdmAt lam cW`, the integral formula `KIntegral` and the majorant
statements `MajorantPointwise`, `LMajBound`, `SeparatedBound`. -/
theorem gramDataLayer : GramDataLayer := by
  intro lam cW hlam hlam1 hAdm hK hMP hLM hSB
  exact gramData hlam hlam1 (cW := cW) hAdm hK hMP hLM hSB

end Line889
