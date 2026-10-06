/-
Simple673/Assembly/Final.lean — the final assembly.

* `simple_bound_673_family`: for an abstract zero configuration `Z` satisfying the
  Riemann–von Mangoldt input, a window family `Pf` with its zero-side package, the second-moment
  statement `GzMoments Z Pf κ` with `κ ≤ C₀`, the Gram data of the family and the finite Gram
  theorem: `(q − ε)·N(T, 2T) ≤ N₀ˢ(T, 2T)` for large `T`, `q = qFinal = 1669159/2478195`.
  The proof follows the upstream endgame `Zeta23.XiPrime.simple_bound_of_gzMoments_family`
  (which is the case `x₁ = b = 0`), with the seam `seam673` in place of `seamA_mult2` and the
  certificate `count_certificate_673`; its organisation is that of
  `Distinct839.dist_bound_839_family`.
* `simple673_dyadic`: the instance for the zeros of the Riemann zeta function.
* `assembly`: the cumulative form `(q − ε)·N(T) ≤ N₀ˢ(T)`, i.e. `AssemblyStatement`.

The span estimate `T·L/(2π) ≤ N(T, 2T) + C·log T` and the estimates `NII, Nedge = o(N)` do not
depend on the window and are those of `Distinct839/Assembly/`.

Namespaces: the deliverable `assembly` is in `Simple673`; every other declaration of
`Simple673/Assembly/` is in `Simple673.Assembly`.
-/
import Zeta23.FinalMult
import Distinct839.Assembly.Final
import Simple673.Assembly.Instance
import Simple673.Assembly.Certificate

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

/-! ### The abstract endgame -/

namespace Simple673.Assembly

open Zeta23 Zeta23.Assembly Zeta23.XiPrime
open Distinct839.Assembly (Nedge eventually_span_le isLittleO_NII isLittleO_Nedge)

section Family

variable (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (P : Params) (hP : P.Valid)
  (hlam : P.lam < 1) {Pf : ℝ → Params} (hW : WindowZeroSide Z P Pf)

include hR hP hlam hW in
/-- **`(q − ε)·N(T, 2T) ≤ N₀ˢ(T, 2T)`** at fixed bandwidth for a window family and an abstract
zero configuration. The Gram data are the family versions of the two halves of
`GramDataStatement`: closeness `GramCloseAt` with an error `η(T) → 0`, and the separated bound
`GramSepAt`, both eventually in `T`. -/
theorem simple_bound_673_family (ha : ∀ᶠ T in atTop, 1 / 4 ≤ (Pf T).a T) {κ : ℝ}
    (hκ : κ ≤ energyC0) (hM : GzMoments Z Pf κ)
    (hclose : ∃ η : ℝ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ T in atTop, GramCloseAt (Pf T) T (η T))
    (hsep : ∀ᶠ T in atTop, GramSepAt (Pf T) T) (hGE : GramEnergyStatement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (qFinal - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
  obtain ⟨C, η₀, hC, hη₀, hseam⟩ := seam673 hGE
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
    (3 - rewX) * (NII Z T : ℝ) + 4 * (Nedge Z T : ℝ) + spanB * (Cs * Real.log T)
      + (7 * rewX + omegaB) + C * η T * ((Z.N T (2 * T) : ℝ) + (NII Z T : ℝ)) with hErrdef
  have hErr : Err =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
    have e1 : (fun T => (3 - rewX) * (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
      hNII.const_mul_left _
    have e2 : (fun T => 4 * (Nedge Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
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
      ≤ (2 + spanB) * (Z.N T (2 * T) : ℝ) + (1 - rewX) * (Z.N0s T (2 * T) : ℝ) + Err T := by
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
  exact count_certificate_673 hκ (N := fun T => (Z.N T (2 * T) : ℝ))
    (tr := fun T => rtrace ((Pf T).hat T (Z.Gz (Pf T) T)))
    (fr := fun T => frobSq ((Pf T).hat T (Z.Gz (Pf T) T)))
    (B := fun T => θ₀ T / ((Pf T).a T * (Pf T).L T)) (lower := fun T => (Z.N0s T (2 * T) : ℝ))
    (Err := Err) (Eventually.of_forall fun T => frobSq_nonneg _) h0 hB0 hBto hErr hNtop
    htrace hfrob

end Family

end Simple673.Assembly

/-! ### The zeros of the Riemann zeta function -/

namespace Simple673.Assembly

open Zeta23

/-- **Dyadic form**: `(q − ε)·N(T, 2T) ≤ N₀ˢ(T, 2T)` for the zeros of `ζ`, from the second-moment
statement, the zero-side package, the Gram data and the finite Gram theorem. -/
theorem simple673_dyadic {lam κ : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam < 1)
    (hκ : κ ≤ energyC0)
    (hM : XiPrime.GzMoments zetaZeroConfig (Pfam lam) κ)
    (hWZ : XiPrime.WindowZeroSide zetaZeroConfig (paramsOf stdProfile lam) (Pfam lam))
    (ha : ∀ᶠ T in atTop, 1 / 4 ≤ (Pfam lam T).a T)
    (hGD : GramDataStatement lam) (hGE : GramEnergyStatement) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (qFinal - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile (lam := lam) (by linarith) hlam1.le
  have h := simple_bound_673_family zetaZeroConfig paperInputs_zeta.RvM (paramsOf stdProfile lam)
    hP hlam1 hWZ ha hκ hM hGD.1 hGD.2 hGE
  simpa using h

end Simple673.Assembly

namespace Simple673

open Zeta23

/-- **The final assembly** (`AssemblyStatement`): for every `ε > 0` and all large `T`,
`(1669159/2478195 − ε)·N(T) ≤ N₀ˢ(T)`, from the layer statements. `N(T)` counts the nontrivial
zeros of the Riemann zeta function with ordinate in `(0, T]` with multiplicity and `N₀ˢ(T)`
counts those that are simple and on the critical line. -/
theorem assembly : AssemblyStatement := by
  intro lam κ hlam hlam1 hκ hM hWZ ha hGD hGE
  have h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (qFinal - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
    cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM (fun _ _ _ => N0simple_add' zetaSeam)
      (Assembly.simple673_dyadic hlam hlam1 hκ hM hWZ ha hGD hGE)
  exact h

end Simple673
