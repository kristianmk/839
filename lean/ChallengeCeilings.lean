/-
ChallengeCeilings.lean — WHAT IS CLAIMED about the limits of the method, from Mathlib alone.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file and the development it belongs to were drafted with Claude (Anthropic),
an AI system, under the direction of the author, who is responsible for their content.

Six theorems about two explicit functions on the real line, the kernels `kernelFirst` and
`kernelSecond`. They are the Fourier transforms of the two windows
`f(u) = 1 + ∑_{j=1}^{n} a_j cos(2π j u)` on `[-1/2, 1/2]`, with `n = 6` cosine terms for the first
window and `n = 10` for the second, that are used in the proofs of

    `distinct_zeros_839` (`Challenge839.lean`): more than 83.90% of the zeros of ζ are distinct,
    `simple_critical_zeros_673` (`Challenge673.lean`): more than 67.35% of the zeros of ζ
        are simple and on the critical line.

Each of these proofs rests on a lower bound for a pair energy `∑ m_i m_j K(y_j - y_i)²`, valid for
every finite set of points on the line with gaps at least `17/20`, by a linear function of the
numbers of points and of the length of the set. Such a lower bound is a *pair-energy certificate*
(`PairCert`, `PairCertAll` for points with multiplicities one and two; `PairCert1`,
`PairCert1All` for simple points). The constants of the two theorems are
`(3 - C₀ + x₂ - x₁ - b)/(2 - 2x₁ + x₂) = 0.83900…` for the certificate `(x₁, x₂, b)` of range six
used in the first proof, and `(2 - C₀ - b)/(1 - x) = 0.67353…` for the certificate `(x, b)` of
range seven used in the second, where `C₀` is a rational upper bound for the energy constant
`C(f)` of the window.

The energy constant of a window `f` is

    `C(f) = ∫ f² + ∬ |s - t| f(s) f(t) ds dt`        (both integrals over `[-1/2, 1/2]`),

and `energyFirst`, `energySecond` are defined below by these integrals for the two windows
(`windowFn`, `windowEnergy`): they are the energy constants as the paper defines them. Their
closed forms (a rational number plus a rational number over `π²`) and their identification with
the constant of the method, the zeta second-moment constant of the window at bandwidth one, are
proved in `SolutionCeilings.lean`.

The theorems below say that these expressions, with `C(f)` itself, are bounded above whatever
the certificate:

    first window:   range 6: < 0.83916,  range 8: < 0.83943,  range 10: < 0.83957,
                    all pairs: < 0.83998;
    second window:  range 7: < 0.67357,  all pairs: < 0.67383.

They are statements about the two windows only, through their kernels and their energy
constants; the zeta function does not occur in them, and the passage from a certificate to a
proportion of zeros is not part of what is claimed here.

This module imports only Mathlib. The `sorry`s are deliberate: this is the statement side.
`SolutionCeilings.lean` repeats the definitions character for character, identifies them with the
definitions of the developments `Distinct839/`, `Simple673/` and `Ceilings/` (the kernels with
the Fourier transforms of the windows `windowFn a`, the energy constants with the constant of the
method), and proves the same six statements.
-/
import Mathlib

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

/-- **First window, range six.** Every pair-energy certificate `(x₁, x₂, b)` of range six (pairs
at index distance at most six, as in an inequality for seven consecutive points) with `b ≥ 0` and
`2 - 2x₁ + x₂ > 0` has `(3 - C(f) + x₂ - x₁ - b)/(2 - 2x₁ + x₂) < 0.83916`. -/
theorem ceiling_range6 {x₁ x₂ b : ℝ} :
    PairCert kernelFirst 6 x₁ x₂ b → 0 ≤ b → 0 < 2 - 2 * x₁ + x₂ →
      (3 - energyFirst + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83916 / 100000 := by
  sorry

/-- **First window, range eight** (inequalities for nine consecutive points): the same expression
is below `0.83943`. -/
theorem ceiling_range8 {x₁ x₂ b : ℝ} :
    PairCert kernelFirst 8 x₁ x₂ b → 0 ≤ b → 0 < 2 - 2 * x₁ + x₂ →
      (3 - energyFirst + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83943 / 100000 := by
  sorry

/-- **First window, range ten** (inequalities for eleven consecutive points): the same expression
is below `0.83957`. -/
theorem ceiling_range10 {x₁ x₂ b : ℝ} :
    PairCert kernelFirst 10 x₁ x₂ b → 0 ≤ b → 0 < 2 - 2 * x₁ + x₂ →
      (3 - energyFirst + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83957 / 100000 := by
  sorry

/-- **First window, all pairs.** Every pair-energy certificate `(x₁, x₂, b)` for all pairs with
`b ≥ 0` and `2 - 2x₁ + x₂ > 0` has `(3 - C(f) + x₂ - x₁ - b)/(2 - 2x₁ + x₂) < 0.83998`: with this
window no lower bound of this kind for the pair energy gives 84%. -/
theorem ceiling_all {x₁ x₂ b : ℝ} :
    PairCertAll kernelFirst x₁ x₂ b → 0 ≤ b → 0 < 2 - 2 * x₁ + x₂ →
      (3 - energyFirst + x₂ - x₁ - b) / (2 - 2 * x₁ + x₂) < 83998 / 100000 := by
  sorry

/-- **Second window, range seven.** Every pair-energy certificate `(x, b)` of range seven (pairs
at index distance at most seven, as in an inequality for eight consecutive points) for simple
points with `b ≥ 0` and `x < 1` has `(2 - C(f) - b)/(1 - x) < 0.67357`. -/
theorem ceiling_line_range7 {x b : ℝ} :
    PairCert1 kernelSecond 7 x b → 0 ≤ b → x < 1 →
      (2 - energySecond - b) / (1 - x) < 67357 / 100000 := by
  sorry

/-- **Second window, all pairs.** Every pair-energy certificate `(x, b)` for simple points and all
pairs with `b ≥ 0` and `x < 1` has `(2 - C(f) - b)/(1 - x) < 0.67383`. -/
theorem ceiling_line_all {x b : ℝ} :
    PairCert1All kernelSecond x b → 0 ≤ b → x < 1 →
      (2 - energySecond - b) / (1 - x) < 67383 / 100000 := by
  sorry
