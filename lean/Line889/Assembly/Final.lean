/-
Line889/Assembly/Final.lean — the final assembly for "simple or on the line" (`assembly`).

* `sl_bound_family`: for an abstract zero configuration `Z` satisfying the Riemann–von Mangoldt
  input, a window family `Pf` with its zero-side package, the second-moment statement
  `GzMoments Z Pf κ` with `κ ≤ C₀`, the Gram data of the family and the finite Gram theorem:

      (q − ε)·N(T, 2T) ≤ N_{s∨0}(T, 2T)    for large `T`,   q = qFinal = 50652159/56956375.

  The seam `seam_sl` gives, for large `T`,

      2t·tr Ĝ − ‖Ĝ‖² − B(2t + 2‖Ĝ‖ + B) ≤ (2t − e₀ + b)·N + (e₀ − e₁)·N_{s∨0} + o(N),

  where the span term `b·TL/(2π)` is at most `b·(N + O(log T))` and the terms with `NII`,
  `Nedge`, the constant `6x + Ω` and `Cη(T)·N` are `o(N)`. The certificate
  `Further.count_certificate` with `a = 2t`, `ν = 2t − e₀ + b`, `μ = e₀ − e₁` and the two moments
  `tr Ĝ ≥ (1 − δ)N`, `‖Ĝ‖² ≤ (κ + δ)N` then gives the constant
  `(a − ν − C₀)/μ = (e₀ − C₀ − b)/(e₀ − e₁) = q` (`qSL_eq`).
* `sl_dyadic`: the instance for the zeros of the Riemann zeta function.
* `assembly`: the cumulative form `(q − ε)·N(T) ≤ N_{s∨0}(T)`, which is `AssemblyStatement` of
  `Line889/Spec2.lean`, by dyadic summation (`Zeta23.cumulative_of_dyadic`, `Zeta23/Main.lean`).

Namespaces: the deliverable `assembly` is in `Line889`; every other declaration of
`Line889/Assembly/` is in `Line889.Assembly`.
-/
import Zeta23.FinalMult
import Distinct839.Assembly.Final
import Further.Certificate
import Line889.Assembly.Instance

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

/-! ### The abstract endgame -/

namespace Line889.Assembly

open Zeta23 Zeta23.Assembly Zeta23.XiPrime
open Further (NsL NsL_add count_certificate zetaZeroConfig_NsL NsimpleOrLine)
open Distinct839.Assembly (Nedge eventually_span_le isLittleO_NII isLittleO_Nedge)

/-- `q = (2t − ν − C₀)/μ` for `ν = 2t − e₀ + b`, `μ = e₀ − e₁`. -/
lemma qSL_eq : (2 * tLev - (2 * tLev - e0C + spanB) - energyC0) / (e0C - e1C) = qFinal := by
  rw [div_eq_iff e0C_sub_e1C_pos.ne', qFinal_mul]; ring

section Family

variable (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (P : Params) (hP : P.Valid)
  (hlam : P.lam < 1) {Pf : ℝ → Params} (hW : WindowZeroSide Z P Pf)

include hR hP hlam hW in
/-- **`(q − ε)·N(T, 2T) ≤ N_{s∨0}(T, 2T)`** at fixed bandwidth for a window family and an abstract
zero configuration, `q = qFinal = 50652159/56956375`. -/
theorem sl_bound_family (ha : ∀ᶠ T in atTop, 1 / 4 ≤ (Pf T).a T) {κ : ℝ}
    (hκ : κ ≤ energyC0) (hM : GzMoments Z Pf κ)
    (hclose : ∃ η : ℝ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ T in atTop, GramCloseAt (Pf T) T (η T))
    (hsep : ∀ᶠ T in atTop, GramSepAt (Pf T) T) (hGE : GramEnergyStatement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (qFinal - ε) * (Z.N T (2 * T) : ℝ) ≤ NsL Z T (2 * T) := by
  obtain ⟨C, η₀, hC, hη₀, hseam⟩ := seam_sl hGE
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
    (2 * tLev - e1C) * (NII Z T : ℝ) + tLev ^ 2 * (Nedge Z T : ℝ) + spanB * (Cs * Real.log T)
      + (6 * rewX + omegaB) + C * η T * ((Z.N T (2 * T) : ℝ) + (NII Z T : ℝ)) with hErrdef
  have hErr : Err =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
    have e1 : (fun T => (2 * tLev - e1C) * (NII Z T : ℝ))
        =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
      hNII.const_mul_left _
    have e2 : (fun T => tLev ^ 2 * (Nedge Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
      hNedge.const_mul_left _
    have e3 : (fun T => spanB * (Cs * Real.log T)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
      (((isLittleO_N_of_isLittleO_Tl Z hR isLittleO_log_Tl).const_mul_left Cs).const_mul_left
        spanB)
    have e4 : (fun _ : ℝ => 6 * rewX + omegaB) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
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
      2 * tLev * rtrace ((Pf T).hat T (Z.Gz (Pf T) T)) - frobSq ((Pf T).hat T (Z.Gz (Pf T) T))
        - θ₀ T / ((Pf T).a T * (Pf T).L T)
          * (2 * tLev + 2 * Real.sqrt (frobSq ((Pf T).hat T (Z.Gz (Pf T) T)))
            + θ₀ T / ((Pf T).a T * (Pf T).L T))
      ≤ (2 * tLev - e0C + spanB) * (Z.N T (2 * T) : ℝ) + (e0C - e1C) * (NsL Z T (2 * T) : ℝ)
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
  -- the certificate with `a = 2t`, `ν = 2t − e₀ + b`, `μ = e₀ − e₁`
  have h := count_certificate (a := 2 * tLev) (ν := 2 * tLev - e0C + spanB) (μ := e0C - e1C)
    (by have := tLev_pos; linarith) e0C_sub_e1C_pos energyC0_pos hκ
    (N := fun T => (Z.N T (2 * T) : ℝ))
    (tr := fun T => rtrace ((Pf T).hat T (Z.Gz (Pf T) T)))
    (fr := fun T => frobSq ((Pf T).hat T (Z.Gz (Pf T) T)))
    (B := fun T => θ₀ T / ((Pf T).a T * (Pf T).L T)) (lower := fun T => (NsL Z T (2 * T) : ℝ))
    (Err := Err) (Eventually.of_forall fun T => frobSq_nonneg _) h0 hB0 hBto hErr hNtop
    htrace hfrob
  rwa [qSL_eq] at h

end Family

/-! ### The zeros of the Riemann zeta function -/

/-- **Dyadic form**: `(q − ε)·N(T, 2T) ≤ N_{s∨0}(T, 2T)` for the zeros of `ζ`, from the
second-moment statement, the zero-side package, the Gram data and the finite Gram theorem. -/
theorem sl_dyadic {lam κ : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam < 1)
    (hκ : κ ≤ energyC0)
    (hM : XiPrime.GzMoments zetaZeroConfig (Pfam lam) κ)
    (hWZ : XiPrime.WindowZeroSide zetaZeroConfig (paramsOf stdProfile lam) (Pfam lam))
    (ha : ∀ᶠ T in atTop, 1 / 4 ≤ (Pfam lam T).a T)
    (hGD : GramDataStatement lam) (hGE : GramEnergyStatement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (qFinal - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ NsimpleOrLine T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile (lam := lam) (by linarith) hlam1.le
  have h := sl_bound_family zetaZeroConfig paperInputs_zeta.RvM (paramsOf stdProfile lam)
    hP hlam1 hWZ ha hκ hM hGD.1 hGD.2 hGE
  simpa using h

/-- Interval additivity of `N_{s∨0}` for the zeros of `ζ`. -/
lemma NsimpleOrLine_add {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    NsimpleOrLine a d = NsimpleOrLine a b + NsimpleOrLine b d := by
  simpa using NsL_add zetaZeroConfig hab hbd

end Line889.Assembly

namespace Line889

open Zeta23

/-- **The final assembly** (`AssemblyStatement` of `Spec2.lean`): from the two moments of the
zero-side matrix with `κ ≤ C₀`, the zero-side package, `a ≥ 1/4`, the Gram data and the finite
Gram theorem, for every `ε > 0` and all large `T`,
`(50652159/56956375 − ε)·N(T) ≤ N_{s∨0}(T)`. Here `N(T)` counts the nontrivial zeros of the
Riemann zeta function with ordinate in `(0, T]` with multiplicity, and `N_{s∨0}(T)` counts, with
multiplicity, those that are simple or on the critical line. -/
theorem assembly : AssemblyStatement := by
  intro lam κ hlam hlam1 hκ hM hWZ ha hGD hGE
  exact cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
    (fun _ _ _ hab hbd => Assembly.NsimpleOrLine_add hab hbd)
    (Assembly.sl_dyadic hlam hlam1 hκ hM hWZ ha hGD hGE)

end Line889
