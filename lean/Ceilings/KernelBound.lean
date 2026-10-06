/-
Ceilings/KernelBound.lean — rational upper bounds for `K²`, for a window with `N` cosine terms.

The kernels of the two windows have the form
`K(t) = sinc(t) + ∑_{j=1}^{N} a_j (sinc(t - j) + sinc(t + j))/2`, with `N = 6` for the first
window and `N = 10` for the second. This file collects what the ceilings need to know about such
a kernel, for every `N` and arbitrary rational coefficients `a : Fin N → ℚ`:

* `kIntGen a n` — the value at an integer `n`: `1` at `0`, `a_{|n|}/2` for `1 ≤ |n| ≤ N` and `0`
  for `|n| > N` (`kernel_int`, `kIntGen_eq_zero`);
* `ratQgen a t = 1/t + ∑_j (-1)^j a_j t/(t² - j²)` — the rational factor of the closed form
  `K(t) = sin(π t)/π · Q(t)` at non-integer `t` (the closed form itself is proved for each window
  in `Distinct839/Kernel/Closed.lean`, `Simple673/Kernel/Closed.lean`);
* `ratQgen_sq_le`: for `t ≥ T > N`, `Q(t)² ≤ E²/t²` with
  `E = |1 + ∑_j (-1)^j a_j| + (∑_j |a_j| j²)/(T² - N²)`, because
  `t Q(t) = 1 + ∑_j (-1)^j a_j + ∑_j (-1)^j a_j j²/(t² - j²)`;
* `KernelEval K Q kI` — the hypotheses under which the rational functions `Q`, `kI` evaluate `K`.
  The last of them is that `K` vanishes at the integers above `intMax = 10`; a kernel of the form
  above satisfies it if `N ≤ 10` (`kIntGen_int_zero`), so it holds for both windows;
* `k2Up Q kI t` — an upper bound for `K(t)²` at every rational `t` (`k2Up_sound`);
* `tailUp Q E2 P N₀ Δ` — an upper bound for `∑_{n ≥ 1} K(Δ + n P)²` for an integer period `P` and
  a non-integer `Δ` (`sum_K_sq_le_tailUp`): `sin²(π(Δ + n P)) = sin²(π Δ)`, the terms `n ≤ N₀` are
  evaluated, and for the rest `Q(y)² ≤ E²/y²` and
  `1/y² ≤ (1/P)(1/(y - P/2) - 1/(y + P/2))` telescopes along `y_n = Δ + n P`;
* `intTailUp kI P` — the same sum for `Δ = 0`: the points `n P` are integers, and `K` vanishes at
  the integers above `intMax`, so that only the terms `n ≤ intMax` occur (`sum_K_sq_int_le`).
-/
import Ceilings.Trig
import Distinct839.Kernel.Basic

noncomputable section

open Real
open scoped BigOperators

namespace Ceilings

open Distinct839 (sincN)
open Distinct839.Kernel (dyHi)

/-! ## Finite sums by recursion -/

/-- `sumN f n = f 0 + … + f (n - 1)`, by recursion on `n` (for evaluation by the kernel). -/
def sumN (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumN f n + f n

theorem sumN_eq (f : ℕ → ℚ) (n : ℕ) : sumN f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN, ih, Finset.sum_range_succ]

theorem cast_sumN (f : ℕ → ℚ) (n : ℕ) :
    ((sumN f n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, ((f i : ℚ) : ℝ) := by
  rw [sumN_eq, Rat.cast_sum]

/-- A sum of nonnegative terms is at most its first `N` terms plus the terms from `N` on. -/
theorem sum_range_le_add {α : Type*} [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (f : ℕ → α) (hf : ∀ n, 0 ≤ f n) (N M : ℕ) :
    ∑ n ∈ Finset.range M, f n ≤ ∑ n ∈ Finset.range N, f n + ∑ x ∈ Finset.range M, f (N + x) := by
  rw [← Finset.sum_range_add]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_add_left M N))
    fun n _ _ => hf n

/-! ## Values at the integers -/

/-- The normalised sinc at an integer. -/
theorem sincN_int (z : ℤ) : sincN (z : ℝ) = if z = 0 then 1 else 0 := by
  by_cases h : z = 0
  · subst h
    simp [Distinct839.sincN]
  · rw [if_neg h]
    exact Distinct839.Kernel.sincN_intCast h

/-- The kernel with coefficients `a` at an integer `n`. -/
theorem kernel_int {N : ℕ} (a : Fin N → ℝ) (n : ℤ) :
    sincN (n : ℝ) + ∑ j : Fin N, a j / 2
        * (sincN ((n : ℝ) - ((j : ℕ) + 1)) + sincN ((n : ℝ) + ((j : ℕ) + 1)))
      = (if n = 0 then 1 else 0) + ∑ j : Fin N, a j / 2
        * ((if n = ((j : ℕ) : ℤ) + 1 then 1 else 0)
            + (if n = -(((j : ℕ) : ℤ) + 1) then 1 else 0)) := by
  rw [sincN_int]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : (n : ℝ) - ((j : ℕ) + 1) = ((n - (((j : ℕ) : ℤ) + 1) : ℤ) : ℝ) := by push_cast; ring
  have e2 : (n : ℝ) + ((j : ℕ) + 1) = ((n + (((j : ℕ) : ℤ) + 1) : ℤ) : ℝ) := by push_cast; ring
  rw [e1, e2, sincN_int, sincN_int]
  congr 2
  · exact if_congr sub_eq_zero rfl rfl
  · exact if_congr add_eq_zero_iff_eq_neg rfl rfl

/-- The value of the kernel with coefficients `a` at the integer `n`, as a rational number. -/
def kIntGen {N : ℕ} (a : Fin N → ℚ) (n : ℤ) : ℚ :=
  (if n = 0 then 1 else 0) + ∑ j : Fin N, a j / 2
    * ((if n = ((j : ℕ) : ℤ) + 1 then 1 else 0) + (if n = -(((j : ℕ) : ℤ) + 1) then 1 else 0))

theorem cast_kIntGen {N : ℕ} (a : Fin N → ℚ) (n : ℤ) :
    ((kIntGen a n : ℚ) : ℝ)
      = (if n = 0 then 1 else 0) + ∑ j : Fin N, ((a j : ℚ) : ℝ) / 2
        * ((if n = ((j : ℕ) : ℤ) + 1 then 1 else 0)
            + (if n = -(((j : ℕ) : ℤ) + 1) then 1 else 0)) := by
  unfold kIntGen
  rw [Rat.cast_add, Rat.cast_sum]
  congr 1
  · split_ifs <;> simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Rat.cast_mul, Rat.cast_add]
    congr 1
    · simp
    · congr 1 <;> split_ifs <;> simp

/-- The kernel with `N` coefficients vanishes at the integers above `N`. -/
theorem kIntGen_eq_zero {N : ℕ} (a : Fin N → ℚ) {n : ℤ} (hn : (N : ℤ) < n) :
    kIntGen a n = 0 := by
  unfold kIntGen
  rw [if_neg (by omega), zero_add]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj := j.isLt
  rw [if_neg (by omega), if_neg (by omega), add_zero, mul_zero]

/-! ## The rational factor of the closed form -/

/-- `Q(t) = 1/t + ∑_j (-1)^j a_j t/(t² - j²)` for the coefficients `a` (index `j - 1`). -/
def ratQgen {N : ℕ} (a : Fin N → ℚ) (t : ℚ) : ℚ :=
  1 / t + ∑ j : Fin N, (-1) ^ ((j : ℕ) + 1) * a j * t / (t ^ 2 - ((j : ℕ) + 1) ^ 2)

/-- `e = 1 + ∑_j (-1)^j a_j`, the limit of `t Q(t)` (the value of the window at `1/2`). -/
def edgeGen {N : ℕ} (a : Fin N → ℚ) : ℚ := 1 + ∑ j : Fin N, (-1) ^ ((j : ℕ) + 1) * a j

/-- `κ = ∑_j |a_j| j²`. -/
def kapGen {N : ℕ} (a : Fin N → ℚ) : ℚ := ∑ j : Fin N, |a j| * (((j : ℕ) : ℚ) + 1) ^ 2

/-- `E² = (|e| + κ/(T² - N²))²`: the constant of the bound `Q(t)² ≤ E²/t²` for `t ≥ T`, for a
kernel with `N` coefficients. -/
def E2gen {N : ℕ} (a : Fin N → ℚ) (T : ℚ) : ℚ :=
  (|edgeGen a| + kapGen a / (T ^ 2 - (N : ℚ) ^ 2)) ^ 2

lemma fin_succ_le {N : ℕ} (j : Fin N) : (((j : ℕ) : ℚ) + 1) ≤ N := by
  have h : (j : ℕ) + 1 ≤ N := j.isLt
  exact_mod_cast h

/-- `t Q(t) = e + ∑_j (-1)^j a_j j²/(t² - j²)` for `t > N`. -/
theorem mul_ratQgen {N : ℕ} (a : Fin N → ℚ) {t : ℚ} (ht : (N : ℚ) < t) :
    t * ratQgen a t = edgeGen a
      + ∑ j : Fin N, (-1) ^ ((j : ℕ) + 1) * a j * (((j : ℕ) : ℚ) + 1) ^ 2
          / (t ^ 2 - (((j : ℕ) : ℚ) + 1) ^ 2) := by
  have hN0 : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have ht0 : t ≠ 0 := by linarith
  unfold ratQgen edgeGen
  rw [mul_add, mul_one_div_cancel ht0, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := fin_succ_le j
  have hj0 : (0 : ℚ) ≤ ((j : ℕ) : ℚ) + 1 := by positivity
  have hD : t ^ 2 - (((j : ℕ) : ℚ) + 1) ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- **The tail bound for `Q`**: `Q(t)² ≤ E²/t²` for `t ≥ T > N`. -/
theorem ratQgen_sq_le {N : ℕ} (a : Fin N → ℚ) {T t : ℚ} (hT : (N : ℚ) < T) (ht : T ≤ t) :
    ratQgen a t ^ 2 ≤ E2gen a T / t ^ 2 := by
  have hN0 : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have htN : (N : ℚ) < t := lt_of_lt_of_le hT ht
  have ht0 : 0 < t := by linarith
  have hTN : 0 < T ^ 2 - (N : ℚ) ^ 2 := by nlinarith
  have hrem : |∑ j : Fin N, (-1) ^ ((j : ℕ) + 1) * a j * (((j : ℕ) : ℚ) + 1) ^ 2
      / (t ^ 2 - (((j : ℕ) : ℚ) + 1) ^ 2)| ≤ kapGen a / (T ^ 2 - (N : ℚ) ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold kapGen
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj := fin_succ_le j
    have hj0 : (0 : ℚ) ≤ ((j : ℕ) : ℚ) + 1 := by positivity
    have hD : T ^ 2 - (N : ℚ) ^ 2 ≤ t ^ 2 - (((j : ℕ) : ℚ) + 1) ^ 2 := by nlinarith
    have hD0 : 0 < t ^ 2 - (((j : ℕ) : ℚ) + 1) ^ 2 := lt_of_lt_of_le hTN hD
    have hnum : |(-1) ^ ((j : ℕ) + 1) * a j * (((j : ℕ) : ℚ) + 1) ^ 2|
        = |a j| * (((j : ℕ) : ℚ) + 1) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (((j : ℕ) : ℚ) + 1)), abs_pow, abs_neg,
        abs_one, one_pow, one_mul]
    rw [abs_div, hnum, abs_of_pos hD0]
    exact div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (sq_nonneg _)) hTN hD
  have habs : |t * ratQgen a t| ≤ |edgeGen a| + kapGen a / (T ^ 2 - (N : ℚ) ^ 2) := by
    rw [mul_ratQgen a htN]
    exact (abs_add_le _ _).trans (add_le_add le_rfl hrem)
  have hsq : (t * ratQgen a t) ^ 2 ≤ E2gen a T := by
    unfold E2gen
    exact sq_le_sq' (by linarith [(abs_le.mp habs).1]) (abs_le.mp habs).2
  have e : ratQgen a t ^ 2 = (t * ratQgen a t) ^ 2 / t ^ 2 := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right hsq (sq_nonneg t)

/-! ## Evaluation of a kernel by rational functions -/

/-- The kernels evaluated below vanish at the integers above `intMax = 10`
(`KernelEval.int_zero`): their windows have at most ten cosine terms, six for the first window
and ten for the second. So the sum of `K²` over the multiples of an integer period (`intTailUp`)
has at most `intMax` terms that do not vanish. -/
def intMax : ℕ := 10

/-- The rational functions `Q` and `kI` evaluate the kernel `K`: `K` is even,
`K(t) = sin(π t)/π · Q(t)` at rational non-integers, `K(n) = kI n` at integers, and `kI n = 0` for
`n > intMax`. -/
structure KernelEval (K : ℝ → ℝ) (Q : ℚ → ℚ) (kI : ℤ → ℚ) : Prop where
  /-- the kernel is even -/
  even : ∀ t, K (-t) = K t
  /-- closed form at rational points that are not integers -/
  closed : ∀ t : ℚ, t.den ≠ 1 → K (t : ℝ) = Real.sin (π * t) / π * ((Q t : ℚ) : ℝ)
  /-- values at the integers -/
  int : ∀ n : ℤ, K (n : ℝ) = ((kI n : ℚ) : ℝ)
  /-- the kernel vanishes at the integers above `intMax` -/
  int_zero : ∀ n : ℤ, (intMax : ℤ) < n → kI n = 0

/-- The last condition of `KernelEval` for a kernel with `N ≤ intMax` coefficients. -/
theorem kIntGen_int_zero {N : ℕ} (a : Fin N → ℚ) (hN : N ≤ intMax) (n : ℤ)
    (hn : (intMax : ℤ) < n) : kIntGen a n = 0 :=
  kIntGen_eq_zero a (lt_of_le_of_lt (by exact_mod_cast hN) hn)

/-- `Q(t)² ≤ E2/t²` for `t ≥ T₀`. -/
structure QTail (Q : ℚ → ℚ) (T₀ E2 : ℚ) : Prop where
  /-- the constant is nonnegative -/
  nonneg : 0 ≤ E2
  /-- the bound -/
  bound : ∀ t : ℚ, T₀ ≤ t → Q t ^ 2 ≤ E2 / t ^ 2

/-- Upper bound for `K(t)²` at a rational point: the exact value at an integer, and
`sUp t · Q(t)²`, rounded upwards, elsewhere. -/
def k2Up (Q : ℚ → ℚ) (kI : ℤ → ℚ) (t : ℚ) : ℚ :=
  if t.den = 1 then kI t.num ^ 2 else dyHi (sUp t * Q t ^ 2)

variable {K : ℝ → ℝ} {Q : ℚ → ℚ} {kI : ℤ → ℚ}

/-- **`K(t)² ≤ k2Up t` for every rational `t`.** -/
theorem k2Up_sound (hK : KernelEval K Q kI) (t : ℚ) :
    K (t : ℝ) ^ 2 ≤ ((k2Up Q kI t : ℚ) : ℝ) := by
  unfold k2Up
  split_ifs with h
  · have ht : ((t.num : ℤ) : ℚ) = t := Rat.coe_int_num_of_den_eq_one h
    have ht' : (t : ℝ) = ((t.num : ℤ) : ℝ) := by
      conv_lhs => rw [← ht]
      exact Rat.cast_intCast _
    rw [ht', hK.int, Rat.cast_pow]
  · rw [hK.closed t h, mul_pow]
    refine Distinct839.Kernel.le_cast_dyHi ?_
    rw [Rat.cast_mul, Rat.cast_pow]
    exact mul_le_mul_of_nonneg_right (sin_div_pi_sq_le t) (sq_nonneg _)

/-! ## The sum over the periods: integer distances -/

/-- Upper bound (in fact the value) of `∑_{n ≥ 1} K(n P)²` for an integer `P ≥ 1`: the terms
`n ≤ intMax`; the others vanish, because `n P > intMax`. -/
def intTailUp (kI : ℤ → ℚ) (P : ℤ) : ℚ :=
  sumN (fun n => kI ((((n : ℕ) : ℤ) + 1) * P) ^ 2) intMax

theorem sum_K_sq_int_le (hK : KernelEval K Q kI) {P : ℤ} (hP : 1 ≤ P) (r : ℕ) :
    ∑ n ∈ Finset.range r, K (((n : ℝ) + 1) * (P : ℝ)) ^ 2 ≤ ((intTailUp kI P : ℚ) : ℝ) := by
  have hval : ∀ n : ℕ, K (((n : ℝ) + 1) * (P : ℝ)) ^ 2
      = (((kI ((((n : ℕ) : ℤ) + 1) * P) ^ 2 : ℚ)) : ℝ) := by
    intro n
    have e : ((n : ℝ) + 1) * (P : ℝ) = (((((n : ℕ) : ℤ) + 1) * P : ℤ) : ℝ) := by push_cast; ring
    rw [e, hK.int, Rat.cast_pow]
  have hzero : ∀ x : ℕ, K ((((intMax + x : ℕ) : ℝ) + 1) * (P : ℝ)) ^ 2 = 0 := by
    intro x
    have hgt : (intMax : ℤ) < (((intMax + x : ℕ) : ℤ) + 1) * P := by
      have h1 : (intMax : ℤ) < ((intMax + x : ℕ) : ℤ) + 1 := by push_cast; omega
      have h0 : (0 : ℤ) ≤ ((intMax + x : ℕ) : ℤ) + 1 := by positivity
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr hP)]
    rw [hval, hK.int_zero _ hgt]
    simp
  calc ∑ n ∈ Finset.range r, K (((n : ℝ) + 1) * (P : ℝ)) ^ 2
      ≤ ∑ n ∈ Finset.range intMax, K (((n : ℝ) + 1) * (P : ℝ)) ^ 2
          + ∑ x ∈ Finset.range r, K ((((intMax + x : ℕ) : ℝ) + 1) * (P : ℝ)) ^ 2 :=
        sum_range_le_add (fun n : ℕ => K (((n : ℝ) + 1) * (P : ℝ)) ^ 2) (fun _ => sq_nonneg _)
          intMax r
    _ = ∑ n ∈ Finset.range intMax, K (((n : ℝ) + 1) * (P : ℝ)) ^ 2 := by
        rw [Finset.sum_eq_zero fun x _ => hzero x, add_zero]
    _ = ((intTailUp kI P : ℚ) : ℝ) := by
        unfold intTailUp
        rw [cast_sumN]
        exact Finset.sum_congr rfl fun n _ => hval n

/-! ## The sum over the periods: non-integer distances -/

/-- A non-integer rational number stays a non-integer when an integer is added. -/
lemma den_add_intCast_ne_one {t : ℚ} (ht : t.den ≠ 1) (z : ℤ) : (t + (z : ℚ)).den ≠ 1 := by
  intro h
  apply ht
  have h1 : (((t + (z : ℚ)).num : ℤ) : ℚ) = t + z := Rat.coe_int_num_of_den_eq_one h
  have h2 : t = (((t + (z : ℚ)).num - z : ℤ) : ℚ) := by
    push_cast
    linarith
  rw [h2]
  exact Rat.den_intCast _

/-- One step of the telescoping bound: `E/(v + P/2)² ≤ (E/P)(1/v - 1/(v + P))`. -/
lemma tele_step {E2 P v : ℚ} (hE : 0 ≤ E2) (hP : 0 < P) (hv : 0 < v) :
    E2 / (v + P / 2) ^ 2 ≤ E2 / P * (1 / v - 1 / (v + P)) := by
  have hvP : 0 < v + P := by linarith
  have e0 : 1 / v - 1 / (v + P) = P / (v * (v + P)) := by
    rw [div_sub_div _ _ hv.ne' hvP.ne']
    congr 1
    ring
  have e : E2 / P * (1 / v - 1 / (v + P)) = E2 / (v * (v + P)) := by
    rw [e0, div_mul_div_comm, mul_comm E2 P, mul_div_mul_left _ _ hP.ne']
  rw [e]
  exact div_le_div_of_nonneg_left hE (mul_pos hv hvP) (by nlinarith [sq_nonneg P])

/-- Telescoping bound for the tail: for `u = Δ + N₀ P + P/2 > 0`,
`∑_{x < k} Q(Δ + (N₀ + x + 1) P)² ≤ (E2/P) (1/u - 1/(u + k P))`. -/
theorem sum_tail_le {T₀ E2 P Δ : ℚ} {N₀ : ℕ} (hQ : QTail Q T₀ E2) (hP : 0 < P)
    (h1 : T₀ ≤ Δ + (N₀ + 1) * P) (h2 : 0 < Δ + N₀ * P + P / 2) (k : ℕ) :
    ∑ x ∈ Finset.range k, Q (Δ + (((N₀ + x : ℕ) : ℚ) + 1) * P) ^ 2
      ≤ E2 / P * (1 / (Δ + N₀ * P + P / 2) - 1 / (Δ + N₀ * P + P / 2 + k * P)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hkP : (0 : ℚ) ≤ (k : ℚ) * P := mul_nonneg (Nat.cast_nonneg k) hP.le
    have hv : 0 < Δ + N₀ * P + P / 2 + k * P := by linarith
    have ev : Δ + N₀ * P + P / 2 + ((k + 1 : ℕ) : ℚ) * P = Δ + N₀ * P + P / 2 + k * P + P := by
      push_cast
      ring
    have ht : Δ + (((N₀ + k : ℕ) : ℚ) + 1) * P = Δ + N₀ * P + P / 2 + k * P + P / 2 := by
      push_cast
      ring
    have hT : T₀ ≤ Δ + N₀ * P + P / 2 + k * P + P / 2 := by linarith
    have hq := hQ.bound _ hT
    have hstep := tele_step hQ.nonneg hP hv
    rw [ht, ev]
    have hmul : E2 / P * (1 / (Δ + N₀ * P + P / 2) - 1 / (Δ + N₀ * P + P / 2 + k * P))
        + E2 / P * (1 / (Δ + N₀ * P + P / 2 + k * P)
            - 1 / (Δ + N₀ * P + P / 2 + k * P + P))
        = E2 / P * (1 / (Δ + N₀ * P + P / 2)
            - 1 / (Δ + N₀ * P + P / 2 + k * P + P)) := by ring
    linarith

/-- Upper bound for `∑_{n ≥ 1} K(Δ + n P)²`, `P` an integer and `Δ` not an integer: the terms
`n ≤ N₀` evaluated (rounded upwards), plus the telescoping tail, times `sUp Δ`. -/
def tailUp (Q : ℚ → ℚ) (E2 : ℚ) (P : ℤ) (N₀ : ℕ) (Δ : ℚ) : ℚ :=
  dyHi (sUp Δ * (sumN (fun n => dyHi (Q (Δ + ((n : ℚ) + 1) * P) ^ 2)) N₀
    + E2 / (P * (Δ + N₀ * P + P / 2))))

/-- The rational part of the tail bound. -/
theorem sum_Q_sq_le {T₀ E2 Δ : ℚ} {P : ℤ} {N₀ : ℕ} (hQ : QTail Q T₀ E2) (hP : 1 ≤ P)
    (h1 : T₀ ≤ Δ + (N₀ + 1) * P) (h2 : 0 < Δ + N₀ * P + P / 2) (r : ℕ) :
    ∑ n ∈ Finset.range r, Q (Δ + ((n : ℚ) + 1) * P) ^ 2
      ≤ sumN (fun n => dyHi (Q (Δ + ((n : ℚ) + 1) * P) ^ 2)) N₀
        + E2 / (P * (Δ + N₀ * P + P / 2)) := by
  have hP0 : (0 : ℚ) < (P : ℚ) := by
    have : (1 : ℚ) ≤ (P : ℚ) := by exact_mod_cast hP
    linarith
  have hr0 : (0 : ℚ) ≤ (r : ℚ) := Nat.cast_nonneg r
  have hsplit := sum_range_le_add (fun n : ℕ => Q (Δ + ((n : ℚ) + 1) * P) ^ 2)
    (fun _ => sq_nonneg _) N₀ r
  have hhead : ∑ n ∈ Finset.range N₀, Q (Δ + ((n : ℚ) + 1) * P) ^ 2
      ≤ sumN (fun n => dyHi (Q (Δ + ((n : ℚ) + 1) * P) ^ 2)) N₀ := by
    rw [sumN_eq]
    exact Finset.sum_le_sum fun n _ => Distinct839.Kernel.le_dyHi _
  have htail := sum_tail_le hQ hP0 h1 h2 r
  have hu' : 0 < Δ + N₀ * P + P / 2 + r * P := by nlinarith
  have hdrop : E2 / P * (1 / (Δ + N₀ * P + P / 2) - 1 / (Δ + N₀ * P + P / 2 + r * P))
      ≤ E2 / (P * (Δ + N₀ * P + P / 2)) := by
    have e : E2 / (P * (Δ + N₀ * P + P / 2)) = E2 / P * (1 / (Δ + N₀ * P + P / 2)) := by
      have hP0' := hP0.ne'
      have h2' := h2.ne'
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hQ.nonneg hP0.le)
    have : 0 ≤ 1 / (Δ + N₀ * P + P / 2 + r * P) := (one_div_pos.mpr hu').le
    linarith
  exact hsplit.trans (add_le_add hhead (htail.trans hdrop))

/-- **The sum over the periods**: `∑_{n=1}^{r} K(Δ + n P)² ≤ tailUp Q E2 P N₀ Δ` for every `r`. -/
theorem sum_K_sq_le_tailUp (hK : KernelEval K Q kI) {T₀ E2 Δ : ℚ} {P : ℤ} {N₀ : ℕ}
    (hQ : QTail Q T₀ E2) (hP : 1 ≤ P) (hΔ : Δ.den ≠ 1)
    (h1 : T₀ ≤ Δ + (N₀ + 1) * P) (h2 : 0 < Δ + N₀ * P + P / 2) (r : ℕ) :
    ∑ n ∈ Finset.range r, K ((Δ : ℝ) + ((n : ℝ) + 1) * (P : ℝ)) ^ 2
      ≤ ((tailUp Q E2 P N₀ Δ : ℚ) : ℝ) := by
  have hterm : ∀ n : ℕ, K ((Δ : ℝ) + ((n : ℝ) + 1) * (P : ℝ)) ^ 2
      ≤ ((sUp Δ : ℚ) : ℝ) * ((Q (Δ + ((n : ℚ) + 1) * P) ^ 2 : ℚ) : ℝ) := by
    intro n
    have ez : Δ + ((n : ℚ) + 1) * (P : ℚ) = Δ + (((((n : ℕ) : ℤ) + 1) * P : ℤ) : ℚ) := by
      push_cast
      ring
    have hden : (Δ + ((n : ℚ) + 1) * (P : ℚ)).den ≠ 1 := by
      rw [ez]
      exact den_add_intCast_ne_one hΔ _
    have hs : sUp (Δ + ((n : ℚ) + 1) * (P : ℚ)) = sUp Δ := by
      rw [ez]
      exact sUp_add_intCast _ _
    have ecast : (Δ : ℝ) + ((n : ℝ) + 1) * (P : ℝ) = ((Δ + ((n : ℚ) + 1) * (P : ℚ) : ℚ) : ℝ) := by
      push_cast
      ring
    rw [ecast, hK.closed _ hden, mul_pow, Rat.cast_pow, ← hs]
    exact mul_le_mul_of_nonneg_right (sin_div_pi_sq_le _) (sq_nonneg _)
  have hs0 : (0 : ℝ) ≤ ((sUp Δ : ℚ) : ℝ) := by exact_mod_cast sUp_nonneg Δ
  have hQsum := sum_Q_sq_le hQ hP h1 h2 r
  have hQsum' : ∑ n ∈ Finset.range r, ((Q (Δ + ((n : ℚ) + 1) * P) ^ 2 : ℚ) : ℝ)
      ≤ ((sumN (fun n => dyHi (Q (Δ + ((n : ℚ) + 1) * P) ^ 2)) N₀
          + E2 / (P * (Δ + N₀ * P + P / 2)) : ℚ) : ℝ) := by
    rw [← Rat.cast_sum]
    exact_mod_cast hQsum
  calc ∑ n ∈ Finset.range r, K ((Δ : ℝ) + ((n : ℝ) + 1) * (P : ℝ)) ^ 2
      ≤ ∑ n ∈ Finset.range r, ((sUp Δ : ℚ) : ℝ) * ((Q (Δ + ((n : ℚ) + 1) * P) ^ 2 : ℚ) : ℝ) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = ((sUp Δ : ℚ) : ℝ) * ∑ n ∈ Finset.range r, ((Q (Δ + ((n : ℚ) + 1) * P) ^ 2 : ℚ) : ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ((sUp Δ : ℚ) : ℝ) * ((sumN (fun n => dyHi (Q (Δ + ((n : ℚ) + 1) * P) ^ 2)) N₀
          + E2 / (P * (Δ + N₀ * P + P / 2)) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hQsum' hs0
    _ ≤ ((tailUp Q E2 P N₀ Δ : ℚ) : ℝ) := by
        unfold tailUp
        refine Distinct839.Kernel.le_cast_dyHi ?_
        rw [Rat.cast_mul]

end Ceilings
