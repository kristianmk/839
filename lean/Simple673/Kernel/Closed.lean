/-
Simple673/Kernel/Closed.lean — the closed form of the kernel away from the integers.

For a real `t` that is not an integer (`K_eq_sin_mul_Qrat`, `deriv_K_eq`),
   `K(t) = sin(π t)/π · Q(t)`,     `Q(t) = 1/t + ∑_{j=1}^{10} (-1)^j a_j t/(t² - j²)`,
   `K'(t) = cos(π t) Q(t) + sin(π t)/π · Q'(t)`,
   `Q'(t) = -1/t² - ∑_{j=1}^{10} (-1)^j a_j (t² + j²)/(t² - j²)²`.
These are the formulas evaluated at the cell midpoints by the kernel table.
-/
import Simple673.Kernel.Deriv

noncomputable section

open Real
open scoped BigOperators Topology

namespace Simple673.Kernel

/-- The rational factor `Q(t) = 1/t + ∑_j (-1)^j a_j t/(t² - j²)` of the kernel. -/
def Qrat (t : ℝ) : ℝ :=
  1 / t + ∑ j : Fin 10, (-1) ^ ((j : ℕ) + 1) * aC j * t / (t ^ 2 - ((j : ℕ) + 1) ^ 2)

/-- The derivative `Q'(t) = -1/t² - ∑_j (-1)^j a_j (t² + j²)/(t² - j²)²`. -/
def Qder (t : ℝ) : ℝ :=
  -1 / t ^ 2 - ∑ j : Fin 10, (-1) ^ ((j : ℕ) + 1) * aC j * (t ^ 2 + ((j : ℕ) + 1) ^ 2)
    / (t ^ 2 - ((j : ℕ) + 1) ^ 2) ^ 2

/-! ## Non-vanishing of the denominators -/

lemma ne_zero_of_notInt {t : ℝ} (ht : ∀ n : ℤ, t ≠ n) : t ≠ 0 := by
  simpa using ht 0

lemma sub_ne_zero_of_notInt {t : ℝ} (ht : ∀ n : ℤ, t ≠ n) (j : ℕ) : t - ((j : ℝ) + 1) ≠ 0 := by
  intro h
  exact ht ((j : ℤ) + 1) (by push_cast; linarith)

lemma add_ne_zero_of_notInt {t : ℝ} (ht : ∀ n : ℤ, t ≠ n) (j : ℕ) : t + ((j : ℝ) + 1) ≠ 0 := by
  intro h
  exact ht (-((j : ℤ) + 1)) (by push_cast; linarith)

lemma sq_sub_sq_ne_zero_of_notInt {t : ℝ} (ht : ∀ n : ℤ, t ≠ n) (j : ℕ) :
    t ^ 2 - ((j : ℝ) + 1) ^ 2 ≠ 0 := by
  rw [show t ^ 2 - ((j : ℝ) + 1) ^ 2 = (t - ((j : ℝ) + 1)) * (t + ((j : ℝ) + 1)) by ring]
  exact mul_ne_zero (sub_ne_zero_of_notInt ht j) (add_ne_zero_of_notInt ht j)

/-! ## The closed form of `K` -/

lemma sincN_sub_nat_succ (t : ℝ) (j : ℕ) (h : t - ((j : ℝ) + 1) ≠ 0) :
    sincN (t - ((j : ℝ) + 1)) = (-1) ^ (j + 1) * Real.sin (π * t) / (π * (t - ((j : ℝ) + 1))) := by
  unfold sincN
  rw [Real.sinc_of_ne_zero (mul_ne_zero pi_ne_zero h)]
  congr 1
  rw [show π * (t - ((j : ℝ) + 1)) = π * t - ((j + 1 : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_sub_nat_mul_pi]

lemma sincN_add_nat_succ (t : ℝ) (j : ℕ) (h : t + ((j : ℝ) + 1) ≠ 0) :
    sincN (t + ((j : ℝ) + 1)) = (-1) ^ (j + 1) * Real.sin (π * t) / (π * (t + ((j : ℝ) + 1))) := by
  unfold sincN
  rw [Real.sinc_of_ne_zero (mul_ne_zero pi_ne_zero h)]
  congr 1
  rw [show π * (t + ((j : ℝ) + 1)) = π * t + ((j + 1 : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_add_nat_mul_pi]

/-- The algebra behind one term of the closed form: partial fractions. -/
lemma closed_term_identity (a s S t m : ℝ) (h1 : t - m ≠ 0) (h2 : t + m ≠ 0) :
    a / 2 * (s * S / (π * (t - m)) + s * S / (π * (t + m)))
      = S / π * (s * a * t / (t ^ 2 - m ^ 2)) := by
  have h3 : t ^ 2 - m ^ 2 ≠ 0 := by
    rw [show t ^ 2 - m ^ 2 = (t - m) * (t + m) by ring]
    exact mul_ne_zero h1 h2
  have hpi : π ≠ 0 := pi_ne_zero
  have e1 : s * S / (π * (t - m)) + s * S / (π * (t + m))
      = s * S * (2 * t) / (π * (t ^ 2 - m ^ 2)) := by
    rw [div_add_div _ _ (mul_ne_zero hpi h1) (mul_ne_zero hpi h2),
      div_eq_div_iff (mul_ne_zero (mul_ne_zero hpi h1) (mul_ne_zero hpi h2)) (mul_ne_zero hpi h3)]
    ring
  have e2 : a / 2 * (s * S * (2 * t) / (π * (t ^ 2 - m ^ 2)))
      = a * (s * S * (2 * t)) / (2 * (π * (t ^ 2 - m ^ 2))) := div_mul_div_comm _ _ _ _
  have e3 : S / π * (s * a * t / (t ^ 2 - m ^ 2)) = S * (s * a * t) / (π * (t ^ 2 - m ^ 2)) :=
    div_mul_div_comm _ _ _ _
  rw [e1, e2, e3,
    div_eq_div_iff (mul_ne_zero two_ne_zero (mul_ne_zero hpi h3)) (mul_ne_zero hpi h3)]
  ring

/-- Closed form of the kernel at non-integer points: `K(t) = sin(π t)/π · Q(t)`. -/
theorem K_eq_sin_mul_Qrat {t : ℝ} (ht : ∀ n : ℤ, t ≠ n) :
    K t = Real.sin (π * t) / π * Qrat t := by
  have ht0 : t ≠ 0 := ne_zero_of_notInt ht
  unfold K Qrat
  rw [mul_add, Finset.mul_sum]
  congr 1
  · unfold sincN
    rw [Real.sinc_of_ne_zero (mul_ne_zero pi_ne_zero ht0), div_mul_div_comm, mul_one]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [sincN_sub_nat_succ t j (sub_ne_zero_of_notInt ht j),
      sincN_add_nat_succ t j (add_ne_zero_of_notInt ht j)]
    exact closed_term_identity _ _ _ _ _ (sub_ne_zero_of_notInt ht j) (add_ne_zero_of_notInt ht j)

/-! ## The derivative -/

lemma hasDerivAt_Qterm (c m t : ℝ) (h : t ^ 2 - m ^ 2 ≠ 0) :
    HasDerivAt (fun s : ℝ => c * s / (s ^ 2 - m ^ 2))
      (-(c * (t ^ 2 + m ^ 2) / (t ^ 2 - m ^ 2) ^ 2)) t := by
  have h1 : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa using (hasDerivAt_id' t).const_mul c
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 - m ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).sub_const (m ^ 2)
  have h3 := h1.fun_div h2 h
  have e : -(c * (t ^ 2 + m ^ 2) / (t ^ 2 - m ^ 2) ^ 2)
      = (c * (t ^ 2 - m ^ 2) - c * t * (2 * t)) / (t ^ 2 - m ^ 2) ^ 2 := by
    rw [← neg_div]
    congr 1
    ring
  rw [e]
  exact h3

/-- `Q` has derivative `Q'` at non-integer points. -/
theorem hasDerivAt_Qrat {t : ℝ} (ht : ∀ n : ℤ, t ≠ n) : HasDerivAt Qrat (Qder t) t := by
  have ht0 : t ≠ 0 := ne_zero_of_notInt ht
  have h0 : HasDerivAt (fun s : ℝ => 1 / s) (-1 / t ^ 2) t := by
    have e1 : (fun s : ℝ => 1 / s) = fun s => s⁻¹ := funext fun s => one_div s
    have e2 : -1 / t ^ 2 = -(t ^ 2)⁻¹ := by rw [neg_div, one_div]
    rw [e1, e2]
    exact hasDerivAt_inv ht0
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ j : Fin 10, (-1) ^ ((j : ℕ) + 1) * aC j * s / (s ^ 2 - ((j : ℕ) + 1) ^ 2))
      (∑ j : Fin 10, -((-1) ^ ((j : ℕ) + 1) * aC j * (t ^ 2 + ((j : ℕ) + 1) ^ 2)
        / (t ^ 2 - ((j : ℕ) + 1) ^ 2) ^ 2)) t :=
    HasDerivAt.fun_sum fun j _ => hasDerivAt_Qterm _ _ t (sq_sub_sq_ne_zero_of_notInt ht j)
  have h := h0.add hsum
  have e : Qder t = -1 / t ^ 2 + ∑ j : Fin 10, -((-1) ^ ((j : ℕ) + 1) * aC j
      * (t ^ 2 + ((j : ℕ) + 1) ^ 2) / (t ^ 2 - ((j : ℕ) + 1) ^ 2) ^ 2) := by
    unfold Qder
    rw [Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [e]
  exact h

/-- The closed form `s ↦ sin(π s)/π · Q(s)` has the expected derivative at non-integer points. -/
theorem hasDerivAt_sin_mul_Qrat {t : ℝ} (ht : ∀ n : ℤ, t ≠ n) :
    HasDerivAt (fun s : ℝ => Real.sin (π * s) / π * Qrat s)
      (Real.cos (π * t) * Qrat t + Real.sin (π * t) / π * Qder t) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.sin (π * s) / π) (Real.cos (π * t)) t := by
    have h := (((hasDerivAt_id' t).const_mul π).sin).div_const π
    have e : Real.cos (π * t) = Real.cos (π * t) * (π * 1) / π := by
      rw [mul_one, mul_div_assoc, div_self pi_ne_zero, mul_one]
    rw [e]
    exact h
  exact h1.mul (hasDerivAt_Qrat ht)

/-- The set of non-integers is a neighbourhood of each of its points. -/
lemma notInt_mem_nhds {t : ℝ} (ht : ∀ n : ℤ, t ≠ n) : {s : ℝ | ∀ n : ℤ, s ≠ n} ∈ 𝓝 t := by
  have hset : {s : ℝ | ∀ n : ℤ, s ≠ n} = (Set.range ((↑) : ℤ → ℝ))ᶜ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
    exact ⟨fun h n hn => h n hn.symm, fun h n hn => h n hn.symm⟩
  rw [hset]
  refine Real.isClosed_range_intCast.isOpen_compl.mem_nhds ?_
  rintro ⟨n, hn⟩
  exact ht n hn.symm

/-- Closed form of the derivative of the kernel at non-integer points:
`K'(t) = cos(π t) Q(t) + sin(π t)/π · Q'(t)`. -/
theorem deriv_K_eq {t : ℝ} (ht : ∀ n : ℤ, t ≠ n) :
    deriv K t = Real.cos (π * t) * Qrat t + Real.sin (π * t) / π * Qder t := by
  have hev : K =ᶠ[𝓝 t] fun s : ℝ => Real.sin (π * s) / π * Qrat s := by
    filter_upwards [notInt_mem_nhds ht] with s hs using K_eq_sin_mul_Qrat hs
  rw [hev.deriv_eq]
  exact (hasDerivAt_sin_mul_Qrat ht).deriv

end Simple673.Kernel
