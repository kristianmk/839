/-
Further/Line/Final.lean — the final assembly for the average.

* `avg_bound_family`: for an abstract zero configuration `Z` satisfying the Riemann–von Mangoldt
  input, a window family `Pf` with its zero-side package, the second-moment statement
  `GzMoments Z Pf κ` with `κ ≤ C₀`, the Gram data of the family and the finite Gram theorem (the
  hypotheses of `Simple673.Assembly.simple_bound_673_family`):

      (1 + q − ε)·N(T, 2T) ≤ N_s(T, 2T) + N₀(T, 2T)    for large `T`,   q = 1669159/2478195.

  The seam `seam_avg` and the certificate `Further.count_certificate` (with `a = 4`,
  `ν = 1 + b`, `μ = 1`) give `(3 − C₀ − b − ε)·N ≤ N_s + N₀ − x₁·N₀ˢ`. The term `x₁·N₀ˢ` is
  bounded from below by the finished theorem `(q − ε)·N ≤ N₀ˢ`, and
  `3 − C₀ − b + x₁·q = 1 + q` because `q·(1 − x₁) = 2 − C₀ − b`.
* `avg_dyadic`: the instance for the zeros of the Riemann zeta function.
* `average_of_layers`: the cumulative form
  `(2073677/2478195 − ε)·N(T) ≤ (N_s(T) + N₀(T))/2`, from the layer statements of `Simple673`;
  `2073677/2478195 = (1 + q)/2`.

Namespaces: the deliverable `average_of_layers` is in `Further`; every other declaration of
`Further/Line/` is in `Further.Line`.
-/
import Zeta23.FinalMult
import Simple673.Assembly.Final
import Further.Certificate
import Further.Line.Instance

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

/-! ### The abstract endgame -/

namespace Further.Line

open Zeta23 Zeta23.Assembly Zeta23.XiPrime
open Simple673 (rewX spanB omegaB energyC0 qFinal GramEnergyStatement GramDataStatement Pfam)
open Simple673.Assembly (GramCloseAt GramSepAt rewX_nonneg one_sub_rewX_pos spanB_nonneg
  energyC0_pos qFinal_mul simple_bound_673_family)
open Distinct839.Assembly (Nedge eventually_span_le isLittleO_NII isLittleO_Nedge)

section Family

variable (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (P : Params) (hP : P.Valid)
  (hlam : P.lam < 1) {Pf : ℝ → Params} (hW : WindowZeroSide Z P Pf)

include hR hP hlam hW in
/-- **`(3 − C₀ − b − ε)·N(T, 2T) ≤ N_s(T, 2T) + N₀(T, 2T) − x₁·N₀ˢ(T, 2T)`** at fixed bandwidth
for a window family and an abstract zero configuration. -/
theorem avg_bound_family_aux (ha : ∀ᶠ T in atTop, 1 / 4 ≤ (Pf T).a T) {κ : ℝ}
    (hκ : κ ≤ energyC0) (hM : GzMoments Z Pf κ)
    (hclose : ∃ η : ℝ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ T in atTop, GramCloseAt (Pf T) T (η T))
    (hsep : ∀ᶠ T in atTop, GramSepAt (Pf T) T) (hGE : GramEnergyStatement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((4 - (1 + spanB) - energyC0) / 1 - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.Ns T (2 * T) : ℝ) + (Z.N0 T (2 * T) : ℝ) - rewX * (Z.N0s T (2 * T) : ℝ) := by
  obtain ⟨C, η₀, hC, hη₀, hseam⟩ := seam_avg hGE
  obtain ⟨η, hηto, hcl⟩ := hclose
  have hL : ∀ T, (Pf T).L T = P.L T := fun T => by simp only [Params.L, hW.lam_eq]
  obtain ⟨θ₀, hTail, hB0, hBto⟩ := family_tail_package Z P hP hlam hW
  obtain ⟨htrace, hfrob⟩ := hM
  obtain ⟨Cs, hspan⟩ := eventually_span_le Z hR P hP
  have hLtop := tendsto_L_atTop P hP.lam_pos
  have hNtop := tendsto_N_atTop Z hR
  have hNII := isLittleO_NII Z hR
  have hNedge := isLittleO_Nedge Z hR
  -- the collected error term
  set Err : ℝ → ℝ := fun T =>
    3 * (NII Z T : ℝ) + (4 + rewX) * (Nedge Z T : ℝ) + spanB * (Cs * Real.log T)
      + (7 * rewX + omegaB) + C * η T * ((Z.N T (2 * T) : ℝ) + (NII Z T : ℝ)) with hErrdef
  have hErr : Err =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
    have e1 : (fun T => 3 * (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
      hNII.const_mul_left _
    have e2 : (fun T => (4 + rewX) * (Nedge Z T : ℝ))
        =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
      hNedge.const_mul_left _
    have e3 : (fun T => spanB * (Cs * Real.log T)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
      (((isLittleO_N_of_isLittleO_Tl Z hR isLittleO_log_Tl).const_mul_left Cs).const_mul_left
        spanB)
    have e4 : (fun _ : ℝ => 7 * rewX + omegaB) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
      isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp hNtop))
    have e5 : (fun T => C * η T * ((Z.N T (2 * T) : ℝ) + (NII Z T : ℝ)))
        =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
      have hCη : Tendsto (fun T => C * η T) atTop (𝓝 0) := by
        simpa using hηto.const_mul C
      have hbig : (fun T => (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ))
          =O[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
        (isBigO_refl _ _).add hNII.isBigO
      exact (isLittleO_of_tendsto_zero_mul
        (g := fun T => (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ)) hCη).trans_isBigO hbig
    exact (((e1.add e2).add e3).add e4).add e5
  -- the seam, eventually
  have h0 : ∀ᶠ T in atTop,
      4 * rtrace ((Pf T).hat T (Z.Gz (Pf T) T)) - frobSq ((Pf T).hat T (Z.Gz (Pf T) T))
        - θ₀ T / ((Pf T).a T * (Pf T).L T)
          * (4 + 2 * Real.sqrt (frobSq ((Pf T).hat T (Z.Gz (Pf T) T)))
            + θ₀ T / ((Pf T).a T * (Pf T).L T))
      ≤ (1 + spanB) * (Z.N T (2 * T) : ℝ)
        + 1 * ((Z.Ns T (2 * T) : ℝ) + (Z.N0 T (2 * T) : ℝ) - rewX * (Z.N0s T (2 * T) : ℝ))
        + Err T := by
    have hηsmall : ∀ᶠ T in atTop, η T ≤ η₀ := hηto.eventually (eventually_le_nhds hη₀)
    filter_upwards [hTail, hW.poisson, ha, eventually_ge_atTop (4 : ℝ),
      hLtop.eventually_gt_atTop 0, hcl, hsep, hηsmall, hspan]
      with T hTl hPo ha4 hT4 hLT hclT hsepT hηT hspT
    have hLpos : 0 < (Pf T).L T := by rw [hL]; exact hLT
    have hη0 : 0 ≤ η T := hclT.nonneg hT4
    have hs := hseam Z T (Pf T) (θ₀ T) (by linarith) hLpos (by linarith) hPo hTl (η T) hη0 hηT
      hclT hsepT
    rw [hL] at hs ⊢
    have hNd : (Z.Nd T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
      exact_mod_cast Z.Nd_le_N T (2 * T)
    have hb : spanB * (T * P.L T / (2 * π))
        ≤ spanB * ((Z.N T (2 * T) : ℝ) + Cs * Real.log T) :=
      mul_le_mul_of_nonneg_left hspT spanB_nonneg
    have hCη : C * η T * ((Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ))
        ≤ C * η T * ((Z.N T (2 * T) : ℝ) + (NII Z T : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hη0)
    simp only [hErrdef]
    linarith
  exact count_certificate (a := 4) (ν := 1 + spanB) (μ := 1) (by norm_num) one_pos
    energyC0_pos hκ (N := fun T => (Z.N T (2 * T) : ℝ))
    (tr := fun T => rtrace ((Pf T).hat T (Z.Gz (Pf T) T)))
    (fr := fun T => frobSq ((Pf T).hat T (Z.Gz (Pf T) T)))
    (B := fun T => θ₀ T / ((Pf T).a T * (Pf T).L T))
    (lower := fun T => (Z.Ns T (2 * T) : ℝ) + (Z.N0 T (2 * T) : ℝ)
      - rewX * (Z.N0s T (2 * T) : ℝ))
    (Err := Err) (Eventually.of_forall fun T => frobSq_nonneg _) h0 hB0 hBto hErr hNtop
    htrace hfrob

include hR hP hlam hW in
/-- **`(1 + q − ε)·N(T, 2T) ≤ N_s(T, 2T) + N₀(T, 2T)`** at fixed bandwidth for a window family and
an abstract zero configuration, `q = 1669159/2478195`. -/
theorem avg_bound_family (ha : ∀ᶠ T in atTop, 1 / 4 ≤ (Pf T).a T) {κ : ℝ}
    (hκ : κ ≤ energyC0) (hM : GzMoments Z Pf κ)
    (hclose : ∃ η : ℝ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ T in atTop, GramCloseAt (Pf T) T (η T))
    (hsep : ∀ᶠ T in atTop, GramSepAt (Pf T) T) (hGE : GramEnergyStatement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 + qFinal - ε) * (Z.N T (2 * T) : ℝ) ≤ (Z.Ns T (2 * T) : ℝ) + (Z.N0 T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, h1⟩ := avg_bound_family_aux Z hR P hP hlam hW ha hκ hM hclose hsep hGE (ε / 2)
    (half_pos hε)
  obtain ⟨T₂, h2⟩ := simple_bound_673_family Z hR P hP hlam hW ha hκ hM hclose hsep hGE (ε / 2)
    (half_pos hε)
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hA := h1 T ((le_max_left _ _).trans hT)
  have hB := h2 T ((le_max_right _ _).trans hT)
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hx0 := rewX_nonneg
  have hx1 := one_sub_rewX_pos
  -- `x₁·(q − ε/2)·N ≤ x₁·N₀ˢ`
  have hxB : rewX * ((qFinal - ε / 2) * (Z.N T (2 * T) : ℝ)) ≤ rewX * (Z.N0s T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_left hB hx0
  -- `q·(1 − x₁)·N = (2 − C₀ − b)·N`
  have hq : qFinal * (1 - rewX) * (Z.N T (2 * T) : ℝ)
      = (2 - energyC0 - spanB) * (Z.N T (2 * T) : ℝ) := by rw [qFinal_mul]
  -- `x₁·(ε/2)·N ≤ (ε/2)·N`
  have hεN : rewX * (ε / 2 * (Z.N T (2 * T) : ℝ)) ≤ 1 * (ε / 2 * (Z.N T (2 * T) : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [div_one] at hA
  linarith

end Family

/-! ### The zeros of the Riemann zeta function -/

/-- **Dyadic form**: `(1 + q − ε)·N(T, 2T) ≤ N_s(T, 2T) + N₀(T, 2T)` for the zeros of `ζ`, from
the second-moment statement, the zero-side package, the Gram data and the finite Gram theorem. -/
theorem avg_dyadic {lam κ : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam < 1)
    (hκ : κ ≤ energyC0)
    (hM : XiPrime.GzMoments zetaZeroConfig (Pfam lam) κ)
    (hWZ : XiPrime.WindowZeroSide zetaZeroConfig (paramsOf stdProfile lam) (Pfam lam))
    (ha : ∀ᶠ T in atTop, 1 / 4 ≤ (Pfam lam T).a T)
    (hGD : GramDataStatement lam) (hGE : GramEnergyStatement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 + qFinal - ε) * (Ncount T (2 * T) : ℝ)
        ≤ ((Nsimple T (2 * T) + N0mult T (2 * T) : ℕ) : ℝ) := by
  have hP := paramsOf_valid taperProfile_stdProfile (lam := lam) (by linarith) hlam1.le
  have h := avg_bound_family zetaZeroConfig paperInputs_zeta.RvM (paramsOf stdProfile lam)
    hP hlam1 hWZ ha hκ hM hGD.1 hGD.2 hGE
  simpa using h

/-- **Cumulative form**: `(1 + q − ε)·N(T) ≤ N_s(T) + N₀(T)` for the zeros of `ζ`. -/
theorem avg_cumulative {lam κ : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam < 1)
    (hκ : κ ≤ energyC0)
    (hM : XiPrime.GzMoments zetaZeroConfig (Pfam lam) κ)
    (hWZ : XiPrime.WindowZeroSide zetaZeroConfig (paramsOf stdProfile lam) (Pfam lam))
    (ha : ∀ᶠ T in atTop, 1 / 4 ≤ (Pfam lam T).a T)
    (hGD : GramDataStatement lam) (hGE : GramEnergyStatement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 + qFinal - ε) * (Ncount 0 T : ℝ) ≤ ((Nsimple 0 T + N0mult 0 T : ℕ) : ℝ) :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
    (f := fun a b => Nsimple a b + N0mult a b)
    (fun a b d hab hbd => by
      have h1 := Ns_add zetaZeroConfig hab hbd
      have h2 := N0_add zetaZeroConfig hab hbd
      simp only [zetaZeroConfig_Ns, zetaZeroConfig_N0] at h1 h2
      simp only [h1, h2]
      ring)
    (avg_dyadic hlam hlam1 hκ hM hWZ ha hGD hGE)

end Further.Line

namespace Further

open Zeta23

/-- **The average of the proportion of simple zeros and the proportion of zeros on the critical
line, conditional on the layer statements of `Simple673`**: for every `ε > 0` and all large `T`,
`(2073677/2478195 − ε)·N(T) ≤ (N_s(T) + N₀(T))/2`. Here `N(T)` counts the nontrivial zeros of the
Riemann zeta function with ordinate in `(0, T]` with multiplicity, `N_s(T)` counts the simple
ones, and `N₀(T)` counts those on the critical line with multiplicity. The hypotheses are those of
`Simple673.AssemblyStatement`. -/
theorem average_of_layers {lam κ : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam < 1)
    (hκ : κ ≤ Simple673.energyC0)
    (hM : XiPrime.GzMoments zetaZeroConfig (Simple673.Pfam lam) κ)
    (hWZ : XiPrime.WindowZeroSide zetaZeroConfig (paramsOf stdProfile lam) (Simple673.Pfam lam))
    (ha : ∀ᶠ T in atTop, 1 / 4 ≤ (Simple673.Pfam lam T).a T)
    (hGD : Simple673.GramDataStatement lam) (hGE : Simple673.GramEnergyStatement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2073677 / 2478195 - ε) * (Ncount 0 T : ℝ)
        ≤ ((Nsimple 0 T : ℝ) + (N0mult 0 T : ℝ)) / 2 := by
  intro ε hε
  obtain ⟨T₀, h⟩ := Line.avg_cumulative hlam hlam1 hκ hM hWZ ha hGD hGE (2 * ε) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := h T hT
  have hq : (1 : ℝ) + Simple673.qFinal = 2 * (2073677 / 2478195) := by
    unfold Simple673.qFinal; norm_num
  rw [hq] at h1
  push_cast at h1
  linarith

end Further
