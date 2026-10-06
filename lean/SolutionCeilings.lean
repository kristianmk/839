/-
SolutionCeilings.lean — the statements of `ChallengeCeilings.lean`, proved.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file and the development it belongs to were drafted with Claude (Anthropic),
an AI system, under the direction of the author, who is responsible for their content.

The definitions of `ChallengeCeilings.lean` (which this file cannot import, because it proves
theorems of the same names) are repeated here character for character. They are then identified
with the definitions of the developments:

* the two windows `windowFn a` are the windows `Distinct839.fCos`, `Simple673.fCos` of the
  developments (`windowFn_first`, `windowFn_second`);
* `kernelFirst = Distinct839.K`, `kernelSecond = Simple673.K` (`kernelFirst_eq`,
  `kernelSecond_eq`), and both are the Fourier transforms of their windows
  (`kernelFirst_eq_integral`, `kernelSecond_eq_integral`; with the windows written as
  `windowFn a`: `kernelFirst_eq_integral_window`, `kernelSecond_eq_integral_window`);
* `separation = Distinct839.sep = Simple673.sep`, `multOf = Distinct839.mulOf`;
* `energyFirst`, `energySecond` are the energy constants as the paper defines them,
  `C(f) = ∫ f² + ∬ |s - t| f(s) f(t) ds dt`. They are the constants of the method:
  `energyFirst = Ceilings.energyC = Distinct839.kappa 1` and
  `energySecond = Ceilings.energyCLine = Simple673.kappa 1` (`energyFirst_eq`,
  `energyFirst_eq_kappa`, `energySecond_eq`, `energySecond_eq_kappa`). The method uses the second
  term in the form `2 ∫₀¹ r (f⋆f)(r) dr`, where `(f⋆f)(r) = ∫ f(s) f(s + r) ds` is the
  autocorrelation `Zeta23.XiPrime.vConv` (`energyFirst_eq_integrals`,
  `energySecond_eq_integrals`); that this equals the double integral is the change of variables
  `Ceilings.two_mul_integral_mul_vConv_eq` of `Ceilings/EnergyIntegral.lean`, proved for every
  continuous function. The closed forms are `energyFirst_closed`, `energySecond_closed`;
* the four certificate predicates are those of `Ceilings/` (`pairCert_first`,
  `pairCertAll_first`, `pairCert1_second`, `pairCert1All_second`).

The six theorems then follow from `Ceilings.ceiling_range6`, `Ceilings.ceiling_range8`,
`Ceilings.ceiling_range10`, `Ceilings.ceiling_all`, `Ceilings.ceiling_line_range7`,
`Ceilings.ceiling_line_all`. This file imports `Ceilings.Main`, which does not contain the two
files `PaperCert.lean` (the only files of `Ceilings/` that depend on a compiled computation).
-/
import Ceilings.Main

section
open scoped BigOperators

noncomputable section

/-- Normalised sinc function: `sin(π t)/(π t)` for `t ≠ 0`, and `1` at `t = 0`. -/
def sincPi (t : ℝ) : ℝ := if t = 0 then 1 else Real.sin (Real.pi * t) / (Real.pi * t)

/-- The kernel of the window `f(u) = 1 + ∑_{j=1}^{n} a_j cos(2π j u)` on `[-1/2, 1/2]` (zero
outside), that is, its Fourier transform
`K(t) = ∫ f(u) cos(2π t u) du = sinc(t) + ∑_{j=1}^{n} a_j (sinc(t - j) + sinc(t + j))/2`,
with `sinc = sincPi`. The argument `a` holds the integers `10⁶ a_j`: entry `j - 1` is `10⁶ a_j`,
and the number `n` of cosine terms is the number of entries of `a`. -/
def windowKernel {n : ℕ} (a : Fin n → ℤ) (t : ℝ) : ℝ :=
  sincPi t + ∑ j : Fin n, (a j : ℝ) / 1000000 / 2
    * (sincPi (t - ((j : ℕ) + 1)) + sincPi (t + ((j : ℕ) + 1)))

/-- The kernel of the first window, the window of the 83.90% theorem for distinct zeros. It has
six cosine terms:
`(a_1, …, a_6) = (0.193305, -0.023105, 0.029166, 0.013952, -0.021009, 0.041052)`. -/
def kernelFirst : ℝ → ℝ := windowKernel ![193305, -23105, 29166, 13952, -21009, 41052]

/-- The kernel of the second window, the window of the 67.35% theorem for simple zeros on the
critical line. It has ten cosine terms: `(a_1, …, a_10) = (0.122290, -0.045012, 0.016241,
0.001887, 0.002711, 0.003731, -0.005307, 0.002982, -0.005153, 0.005358)`. -/
def kernelSecond : ℝ → ℝ :=
  windowKernel ![122290, -45012, 16241, 1887, 2711, 3731, -5307, 2982, -5153, 5358]

/-- The separation `θ = 17/20`: in all configurations below, any two points are at least `θ`
apart. -/
def separation : ℝ := 17 / 20

/-- The window `f(u) = 1 + ∑_{j=1}^{n} a_j cos(2π j u)` whose kernel is `windowKernel a`, as a
function on the whole real line; the restriction to `[-1/2, 1/2]` is in the limits of the
integrals of `windowEnergy`. As for `windowKernel`, entry `j - 1` of `a` is `10⁶ a_j`. -/
def windowFn {n : ℕ} (a : Fin n → ℤ) (u : ℝ) : ℝ :=
  1 + ∑ j : Fin n, (a j : ℝ) / 1000000 * Real.cos (2 * Real.pi * ((j : ℕ) + 1) * u)

/-- The energy constant of the window `f = windowFn a`:
`C(f) = ∫ f² + ∬ |s - t| f(s) f(t) ds dt`, both integrals over `[-1/2, 1/2]`. -/
def windowEnergy {n : ℕ} (a : Fin n → ℤ) : ℝ :=
  (∫ u in (-(1 : ℝ) / 2)..(1 / 2), windowFn a u ^ 2)
    + ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
        |s - t| * windowFn a s * windowFn a t

/-- The energy constant `C(f) = ∫ f² + ∬ |s - t| f(s) f(t) ds dt` of the first window, the window
of `kernelFirst`. Its value is `1.3327049582…`. In closed form (`energyFirst_closed` in
`SolutionCeilings.lean`): `∫ f² = 1 + ½ ∑ a_j² = 408214524539/400000000000`, and
`∬ |s - t| f(s) f(t) ds dt = 1/3 + π⁻² ∑_j ((-1)^j a_j/j² - a_j²/(4j²))
= 1/3 - (250664498438947/1200000000000000)/π²`. -/
def energyFirst : ℝ := windowEnergy ![193305, -23105, 29166, 13952, -21009, 41052]

/-- The energy constant `C(f) = ∫ f² + ∬ |s - t| f(s) f(t) ds dt` of the second window, the window
of `kernelSecond`. Its value is `1.3279472728…`. In closed form (`energySecond_closed` in
`SolutionCeilings.lean`): `∫ f² = 1 + ½ ∑ a_j² = 1008680921561/1000000000000`, and
`∬ |s - t| f(s) f(t) ds dt = 1/3 + π⁻² ∑_j ((-1)^j a_j/j² - a_j²/(4j²))
= 1/3 - (440830631846157799/3175200000000000000)/π²`. -/
def energySecond : ℝ :=
  windowEnergy ![122290, -45012, 16241, 1887, 2711, 3731, -5307, 2982, -5153, 5358]

/-- Multiplicity of a label: label `0` is a simple point (multiplicity `1`), label `1` a double
point (multiplicity `2`). -/
def multOf (a : Fin 2) : ℝ := (a : ℕ) + 1

/-- **Pair-energy certificate of range `s`** for the kernel `K`, labelled points. The triple
`(x₁, x₂, b)` is a certificate if there is a constant `C₃` such that for every finite chain
`y_0 < y_1 < … < y_{ℓ-1}` of real numbers, any two at least `17/20` apart, every labelling `lab`
of its points as simple or double, and every `R ≥ 0` with `y_j - y_i ≤ R` for all `i, j` (the
chain lies in an interval of length `R`),

    `x₁ n₁ + x₂ n₂ - b R - C₃ ≤ ∑_{i ≠ j, |i - j| ≤ s} m_i m_j K(y_j - y_i)²`.

Here `n₁`, `n₂` are the numbers of simple and of double points (the left side is written
`∑ i, (if lab i = 0 then x₁ else x₂)`), `m_i ∈ {1, 2}` are the multiplicities, and the sum is over
the ordered pairs of different points at index distance at most `s`. -/
def PairCert (K : ℝ → ℝ) (s : ℕ) (x₁ x₂ b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (lab : Fin ℓ → Fin 2) (R : ℝ),
    (∀ i j, i < j → separation ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    ∑ i : Fin ℓ, (if lab i = 0 then x₁ else x₂) - b * R - C₃
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (s : ℤ) then
          multOf (lab i) * multOf (lab j) * K (y j - y i) ^ 2 else 0

/-- **Pair-energy certificate, all pairs**, for the kernel `K`, labelled points: as `PairCert`,
with the sum over all ordered pairs of different points,

    `x₁ n₁ + x₂ n₂ - b R - C₃ ≤ ∑_{i ≠ j} m_i m_j K(y_j - y_i)²`. -/
def PairCertAll (K : ℝ → ℝ) (x₁ x₂ b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (lab : Fin ℓ → Fin 2) (R : ℝ),
    (∀ i j, i < j → separation ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    ∑ i : Fin ℓ, (if lab i = 0 then x₁ else x₂) - b * R - C₃
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ,
          if i ≠ j then multOf (lab i) * multOf (lab j) * K (y j - y i) ^ 2 else 0

/-- **Pair-energy certificate of range `s`** for the kernel `K`, simple points (no labels). The
pair `(x, b)` is a certificate if there is a constant `C₃` such that for every finite chain
`y_0 < y_1 < … < y_{ℓ-1}` of real numbers, any two at least `17/20` apart, and every `R ≥ 0` with
`y_j - y_i ≤ R` for all `i, j`,

    `x ℓ - b R - C₃ ≤ ∑_{i ≠ j, |i - j| ≤ s} K(y_j - y_i)²`. -/
def PairCert1 (K : ℝ → ℝ) (s : ℕ) (x b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (R : ℝ),
    (∀ i j, i < j → separation ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    x * ℓ - b * R - C₃
      ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (s : ℤ) then
          K (y j - y i) ^ 2 else 0

/-- **Pair-energy certificate, all pairs**, for the kernel `K`, simple points: as `PairCert1`,
with the sum over all ordered pairs of different points,

    `x ℓ - b R - C₃ ≤ ∑_{i ≠ j} K(y_j - y_i)²`. -/
def PairCert1All (K : ℝ → ℝ) (x b : ℝ) : Prop :=
  ∃ C₃ : ℝ, ∀ (ℓ : ℕ) (y : Fin ℓ → ℝ) (R : ℝ),
    (∀ i j, i < j → separation ≤ y j - y i) → 0 ≤ R → (∀ i j, y j - y i ≤ R) →
    x * ℓ - b * R - C₃ ≤ ∑ i : Fin ℓ, ∑ j : Fin ℓ, if i ≠ j then K (y j - y i) ^ 2 else 0

end
end

/-! ## The definitions above are those of the developments -/

/-- The first window `windowFn a` is the window of `Distinct839`. -/
theorem windowFn_first :
    windowFn ![193305, -23105, 29166, 13952, -21009, 41052] = Distinct839.fCos := by
  funext u
  rfl

/-- The second window `windowFn a` is the window of `Simple673`. -/
theorem windowFn_second :
    windowFn ![122290, -45012, 16241, 1887, 2711, 3731, -5307, 2982, -5153, 5358]
      = Simple673.fCos := by
  funext u
  rfl

/-- `sincPi` is the normalised sinc of the developments. -/
theorem sincPi_eq (t : ℝ) : sincPi t = Distinct839.sincN t := by
  unfold sincPi Distinct839.sincN
  by_cases h : t = 0
  · subst h
    simp
  · rw [if_neg h, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero h)]

/-- The first kernel is the kernel of `Distinct839`. -/
theorem kernelFirst_eq : kernelFirst = Distinct839.K := by
  funext t
  unfold kernelFirst windowKernel Distinct839.K
  simp only [sincPi_eq]
  rfl

/-- The second kernel is the kernel of `Simple673`. -/
theorem kernelSecond_eq : kernelSecond = Simple673.K := by
  funext t
  unfold kernelSecond windowKernel Simple673.K
  simp only [sincPi_eq]
  rfl

/-- The first kernel is the Fourier transform of the first window
`Distinct839.fCos u = 1 + ∑ a_j cos(2π j u)` on `[-1/2, 1/2]`. -/
theorem kernelFirst_eq_integral (t : ℝ) :
    kernelFirst t
      = ∫ u in (-(1 : ℝ) / 2)..(1 / 2), Distinct839.fCos u * Real.cos (2 * Real.pi * t * u) := by
  rw [kernelFirst_eq]
  exact Distinct839.K_eq_integral t

/-- The second kernel is the Fourier transform of the second window `Simple673.fCos`. -/
theorem kernelSecond_eq_integral (t : ℝ) :
    kernelSecond t
      = ∫ u in (-(1 : ℝ) / 2)..(1 / 2), Simple673.fCos u * Real.cos (2 * Real.pi * t * u) := by
  rw [kernelSecond_eq]
  exact Simple673.K_eq_integral t

/-- The first kernel is the Fourier transform of the first window, with the window written as
`windowFn a`: the kernel and the energy constant `energyFirst` belong to the same window. -/
theorem kernelFirst_eq_integral_window (t : ℝ) :
    kernelFirst t
      = ∫ u in (-(1 : ℝ) / 2)..(1 / 2),
          windowFn ![193305, -23105, 29166, 13952, -21009, 41052] u
            * Real.cos (2 * Real.pi * t * u) := by
  rw [windowFn_first]
  exact kernelFirst_eq_integral t

/-- The second kernel is the Fourier transform of the second window, with the window written as
`windowFn a`: the kernel and the energy constant `energySecond` belong to the same window. -/
theorem kernelSecond_eq_integral_window (t : ℝ) :
    kernelSecond t
      = ∫ u in (-(1 : ℝ) / 2)..(1 / 2),
          windowFn ![122290, -45012, 16241, 1887, 2711, 3731, -5307, 2982, -5153, 5358] u
            * Real.cos (2 * Real.pi * t * u) := by
  rw [windowFn_second]
  exact kernelSecond_eq_integral t

theorem separation_eq_first : separation = Distinct839.sep := rfl

theorem separation_eq_second : separation = Simple673.sep := rfl

theorem multOf_eq (a : Fin 2) : multOf a = Distinct839.mulOf a := rfl

/-- The first energy constant is the constant of `Ceilings/`: `∫ f² = A`
(`Distinct839.Constant.integral_fCos_sq`), and `∬ |s - t| f(s) f(t) ds dt = B`
(`Ceilings.integral_abs_sub_mul_fCos`, from the change of variables
`Ceilings.two_mul_integral_mul_vConv_eq`). -/
theorem energyFirst_eq : energyFirst = Ceilings.energyC := by
  unfold energyFirst windowEnergy Ceilings.energyC
  rw [windowFn_first, Distinct839.Constant.integral_fCos_sq, Ceilings.integral_abs_sub_mul_fCos]

/-- The first energy constant is the constant of the method: the zeta second-moment constant of
the first window at bandwidth `λ = 1`. -/
theorem energyFirst_eq_kappa : energyFirst = Distinct839.kappa 1 :=
  energyFirst_eq.trans Ceilings.energyC_eq_kappa_one

/-- **Closed form of the first energy constant**: a rational number plus a rational number over
`π²`. -/
theorem energyFirst_closed :
    energyFirst
      = 408214524539 / 400000000000
        + (1 / 3 - 250664498438947 / 1200000000000000 / Real.pi ^ 2) := by
  rw [energyFirst_eq]
  unfold Ceilings.energyC
  rw [Distinct839.Constant.Aconst_eq, Distinct839.Constant.Bconst_eq]

/-- The first energy constant in the form in which the method uses it, for the window
`f = Distinct839.fCos`: `∫ f² + 2 ∫₀¹ r (f⋆f)(r) dr`. -/
theorem energyFirst_eq_integrals :
    energyFirst = (∫ s in (-(1 : ℝ) / 2)..(1 / 2), Distinct839.fCos s ^ 2)
      + 2 * ∫ r in (0 : ℝ)..1, r * Zeta23.XiPrime.vConv Distinct839.fCos r := by
  rw [Distinct839.Constant.integral_fCos_sq, Distinct839.Constant.integral_mul_vConv_fCos,
    energyFirst_eq]
  unfold Ceilings.energyC
  ring

/-- The second energy constant is the constant of `Ceilings/`: `∫ f² = A`
(`Simple673.Constant.integral_fCos_sq`), and `∬ |s - t| f(s) f(t) ds dt = B`
(`Ceilings.integral_abs_sub_mul_fCos_line`, from the change of variables
`Ceilings.two_mul_integral_mul_vConv_eq`). -/
theorem energySecond_eq : energySecond = Ceilings.energyCLine := by
  unfold energySecond windowEnergy Ceilings.energyCLine
  rw [windowFn_second, Simple673.Constant.integral_fCos_sq,
    Ceilings.integral_abs_sub_mul_fCos_line]

/-- The second energy constant is the constant of the method for the second window. -/
theorem energySecond_eq_kappa : energySecond = Simple673.kappa 1 :=
  energySecond_eq.trans Ceilings.energyCLine_eq_kappa_one

/-- **Closed form of the second energy constant**: a rational number plus a rational number over
`π²`. -/
theorem energySecond_closed :
    energySecond
      = 1008680921561 / 1000000000000
        + (1 / 3 - 440830631846157799 / 3175200000000000000 / Real.pi ^ 2) := by
  rw [energySecond_eq]
  unfold Ceilings.energyCLine
  rw [Simple673.Constant.Aconst_eq, Simple673.Constant.Bconst_eq]

/-- The second energy constant in the form in which the method uses it, for the window
`f = Simple673.fCos`: `∫ f² + 2 ∫₀¹ r (f⋆f)(r) dr`. -/
theorem energySecond_eq_integrals :
    energySecond = (∫ s in (-(1 : ℝ) / 2)..(1 / 2), Simple673.fCos s ^ 2)
      + 2 * ∫ r in (0 : ℝ)..1, r * Zeta23.XiPrime.vConv Simple673.fCos r := by
  rw [Simple673.Constant.integral_fCos_sq, Simple673.Constant.integral_mul_vConv_fCos,
    energySecond_eq]
  unfold Ceilings.energyCLine
  ring

/-- Certificates of range `s` for the first kernel are those of `Ceilings/`. -/
theorem pairCert_first {s : ℕ} {x₁ x₂ b : ℝ} :
    PairCert kernelFirst s x₁ x₂ b ↔ Ceilings.PairCert s x₁ x₂ b := by
  rw [kernelFirst_eq]
  exact Iff.rfl

/-- Certificates for all pairs for the first kernel are those of `Ceilings/`. -/
theorem pairCertAll_first {x₁ x₂ b : ℝ} :
    PairCertAll kernelFirst x₁ x₂ b ↔ Ceilings.PairCertAll x₁ x₂ b := by
  rw [kernelFirst_eq]
  exact Iff.rfl

/-- Certificates of range `s` for simple points and the second kernel are those of `Ceilings/`. -/
theorem pairCert1_second {s : ℕ} {x b : ℝ} :
    PairCert1 kernelSecond s x b ↔ Ceilings.PairCert1 s x b := by
  rw [kernelSecond_eq]
  exact Iff.rfl

/-- Certificates for all pairs for simple points and the second kernel are those of
`Ceilings/`. -/
theorem pairCert1All_second {x b : ℝ} :
    PairCert1All kernelSecond x b ↔ Ceilings.PairCert1All x b := by
  rw [kernelSecond_eq]
  exact Iff.rfl

/-! ## The six statements -/

/-- **First window, range six.** Every pair-energy certificate `(x₁, x₂, b)` of range six (pairs
at index distance at most six, as in an inequality for seven consecutive points) with `b ≥ 0` and
`2 - 2x₁ + x₂ > 0` has `(3 - C(f) + x₂ - x₁ - b)/(2 - 2x₁ + x₂) < 0.83916`. -/
theorem ceiling_range6 {x₁ x₂ b : ℝ} :
    PairCert kernelFirst 6 x₁ x₂ b → 0 ≤ b → 0 < 2 - 2 * x₁ + x₂ →
      (3 - energyFirst + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83916 / 100000 := by
  intro h hb hD
  rw [energyFirst_eq]
  exact Ceilings.ceiling_range6 (pairCert_first.mp h) hb hD

/-- **First window, range eight** (inequalities for nine consecutive points): the same expression
is below `0.83943`. -/
theorem ceiling_range8 {x₁ x₂ b : ℝ} :
    PairCert kernelFirst 8 x₁ x₂ b → 0 ≤ b → 0 < 2 - 2 * x₁ + x₂ →
      (3 - energyFirst + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83943 / 100000 := by
  intro h hb hD
  rw [energyFirst_eq]
  exact Ceilings.ceiling_range8 (pairCert_first.mp h) hb hD

/-- **First window, range ten** (inequalities for eleven consecutive points): the same expression
is below `0.83957`. -/
theorem ceiling_range10 {x₁ x₂ b : ℝ} :
    PairCert kernelFirst 10 x₁ x₂ b → 0 ≤ b → 0 < 2 - 2 * x₁ + x₂ →
      (3 - energyFirst + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83957 / 100000 := by
  intro h hb hD
  rw [energyFirst_eq]
  exact Ceilings.ceiling_range10 (pairCert_first.mp h) hb hD

/-- **First window, all pairs.** Every pair-energy certificate `(x₁, x₂, b)` for all pairs with
`b ≥ 0` and `2 - 2x₁ + x₂ > 0` has `(3 - C(f) + x₂ - x₁ - b)/(2 - 2x₁ + x₂) < 0.83998`: with this
window no lower bound of this kind for the pair energy gives 84%. -/
theorem ceiling_all {x₁ x₂ b : ℝ} :
    PairCertAll kernelFirst x₁ x₂ b → 0 ≤ b → 0 < 2 - 2 * x₁ + x₂ →
      (3 - energyFirst + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83998 / 100000 := by
  intro h hb hD
  rw [energyFirst_eq]
  exact Ceilings.ceiling_all (pairCertAll_first.mp h) hb hD

/-- **Second window, range seven.** Every pair-energy certificate `(x, b)` of range seven (pairs
at index distance at most seven, as in an inequality for eight consecutive points) for simple
points with `b ≥ 0` and `x < 1` has `(2 - C(f) - b)/(1 - x) < 0.67357`. -/
theorem ceiling_line_range7 {x b : ℝ} :
    PairCert1 kernelSecond 7 x b → 0 ≤ b → x < 1 →
      (2 - energySecond - b) / (1 - x) < 67357 / 100000 := by
  intro h hb hx
  rw [energySecond_eq]
  exact Ceilings.ceiling_line_range7 (pairCert1_second.mp h) hb hx

/-- **Second window, all pairs.** Every pair-energy certificate `(x, b)` for simple points and all
pairs with `b ≥ 0` and `x < 1` has `(2 - C(f) - b)/(1 - x) < 0.67383`. -/
theorem ceiling_line_all {x b : ℝ} :
    PairCert1All kernelSecond x b → 0 ≤ b → x < 1 →
      (2 - energySecond - b) / (1 - x) < 67383 / 100000 := by
  intro h hb hx
  rw [energySecond_eq]
  exact Ceilings.ceiling_line_all (pairCert1All_second.mp h) hb hx
