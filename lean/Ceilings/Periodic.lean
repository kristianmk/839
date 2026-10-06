/-
Ceilings/Periodic.lean — a certificate tested on a periodic configuration.

A periodic configuration is given by sequences indexed by `ℕ`: positions `p` with
`p (a + m) = p a + P` (`m` points per period, period `P`) and weights `d` with `d (a + m) = d a`.
Its first `M m` points form `M` periods. The file proves, for an even kernel `K`:

* `chainEnergy_eq_sum`: the energy of a finite chain as a sum over the pairs `(a, a + s + 1)`;
* `chainEnergy_le_mul`: the energy of the pairs of index distance at most `r` among the first `M m`
  points is at most `M` times the energy per period
  `periodEnergy K d p m r = ∑_{i < m} ∑_{s < r} 2 d_i d_{i+s+1} K(p_{i+s+1} - p_i)²`
  (the finite chain has fewer pairs: those cut at the right end are missing, and all terms are
  nonnegative);
* `le_of_forall_nat_mul_sub_le`: if `M A - C ≤ M e` for all `M`, then `A ≤ e`;
* `PairCertFor.star`, `PairCert1For.star`: a certificate `(x₁, x₂, b)` of range `r`, applied to
  `M` periods, divided by `M`, with `M → ∞`, gives inequality (⋆)
  `x₁ n₁ + x₂ n₂ - b P ≤ periodEnergy … r`;
* `PairCertAllFor.star`, `PairCert1AllFor.star`: for a certificate for all pairs, `M` periods have
  only pairs of index distance below `M m`, so (⋆) holds with any common upper bound `e` for the
  energies `periodEnergy … r`, `r = 0, 1, 2, …`. No infinite series is needed.

* `periodEnergy_le_all`: a bound for the energies per period of all ranges at once, by regrouping
  the pairs `(i, i + s)` according to the period `n` of the second point
  (`sum_shift_le_period_sum`); what remains to bound are the sums `∑_{n ≥ 1} K(p_{i'} - p_i + n P)²`.

Nothing here depends on a window.
-/
import Ceilings.Defs
import Distinct839.Transfer.Sums

open scoped BigOperators
open Finset

namespace Ceilings

open Distinct839 (mulOf)

/-! ## Periodic sequences -/

/-- A sequence of period `m` is invariant under shifts by multiples of `m`. -/
theorem periodic_add_mul {α : Type*} (f : ℕ → α) (m : ℕ) (hf : ∀ a, f (a + m) = f a) (i M : ℕ) :
    f (i + M * m) = f i := by
  induction M with
  | zero => simp
  | succ M ih => rw [add_mul, one_mul, ← add_assoc, hf, ih]

/-- Positions of a periodic configuration: a shift by `M` periods adds `M P`. -/
theorem shift_add_mul (p : ℕ → ℝ) (m : ℕ) (P : ℝ) (hp : ∀ a, p (a + m) = p a + P) (i M : ℕ) :
    p (i + M * m) = p i + M * P := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [add_mul, one_mul, ← add_assoc, hp, ih]
    push_cast
    ring

/-- A sum over `M m` consecutive indices, by periods. -/
theorem sum_range_mul (f : ℕ → ℝ) (m M : ℕ) :
    ∑ a ∈ range (M * m), f a = ∑ u ∈ range M, ∑ i ∈ range m, f (u * m + i) := by
  induction M with
  | zero => simp
  | succ M ih => rw [add_mul, one_mul, sum_range_add, ih, sum_range_succ]

/-- The sum of a periodic sequence over `M` periods. -/
theorem sum_range_mul_periodic (f : ℕ → ℝ) (m : ℕ) (hf : ∀ a, f (a + m) = f a) (M : ℕ) :
    ∑ a ∈ range (M * m), f a = (M : ℝ) * ∑ i ∈ range m, f i := by
  rw [sum_range_mul]
  have h : ∀ u ∈ range M, ∑ i ∈ range m, f (u * m + i) = ∑ i ∈ range m, f i := fun u _ =>
    sum_congr rfl fun i _ => by rw [add_comm, periodic_add_mul f m hf]
  rw [sum_congr rfl h, sum_const, card_range, nsmul_eq_mul]

/-! ## The two energies -/

/-- Energy of the pairs of index distance at most `r` among the first `n` points of the sequence
`p` with weights `d` (ordered pairs, as in `PairCertFor`). -/
def chainEnergy (K : ℝ → ℝ) (r : ℕ) (d p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ range n, ∑ c ∈ range n,
    if a ≠ c ∧ |(a : ℤ) - (c : ℤ)| ≤ (r : ℤ) then d a * d c * K (p c - p a) ^ 2 else 0

/-- Pair energy per period, pairs of index distance at most `r`:
`∑_{i < m} ∑_{s < r} 2 d_i d_{i+s+1} K(p_{i+s+1} - p_i)²`. -/
def periodEnergy (K : ℝ → ℝ) (d p : ℕ → ℝ) (m r : ℕ) : ℝ :=
  ∑ i ∈ range m, ∑ s ∈ range r, 2 * d i * d (i + s + 1) * K (p (i + s + 1) - p i) ^ 2

/-- The energy of a finite chain, written with the pairs `(a, a + s + 1)`, `s < r`, that lie
inside the chain: each unordered pair is counted twice, and the kernel is even. -/
theorem chainEnergy_eq_sum {K : ℝ → ℝ} (hK : ∀ t, K (-t) = K t) (r : ℕ) (d p : ℕ → ℝ) (n : ℕ) :
    chainEnergy K r d p n
      = ∑ a ∈ range n, ∑ s ∈ range r,
          if a + s + 1 < n then 2 * d a * d (a + s + 1) * K (p (a + s + 1) - p a) ^ 2
          else 0 := by
  unfold chainEnergy
  have h1 : ∀ a c : ℕ,
      (if a ≠ c ∧ |(a : ℤ) - (c : ℤ)| ≤ (r : ℤ) then d a * d c * K (p c - p a) ^ 2 else 0)
        = if a ≠ c then
            (if |(a : ℤ) - (c : ℤ)| ≤ (r : ℤ) then d a * d c * K (p c - p a) ^ 2 else 0)
          else 0 := by
    intro a c
    by_cases h : a ≠ c
    · rw [if_pos h]
      by_cases h' : |(a : ℤ) - (c : ℤ)| ≤ (r : ℤ)
      · rw [if_pos ⟨h, h'⟩, if_pos h']
      · rw [if_neg (fun hh => h' hh.2), if_neg h']
    · rw [if_neg h, if_neg (fun hh => h hh.1)]
  simp_rw [h1]
  rw [Distinct839.Transfer.sum_offdiag_eq n (fun a c =>
    if |(a : ℤ) - (c : ℤ)| ≤ (r : ℤ) then d a * d c * K (p c - p a) ^ 2 else 0)]
  refine sum_congr rfl fun a _ => ?_
  have hpt : ∀ c : ℕ,
      (if a < c then
          (if |(a : ℤ) - (c : ℤ)| ≤ (r : ℤ) then d a * d c * K (p c - p a) ^ 2 else 0)
          + (if |(c : ℤ) - (a : ℤ)| ≤ (r : ℤ) then d c * d a * K (p a - p c) ^ 2 else 0)
        else 0)
        = if a + 1 ≤ c ∧ c < a + r + 1 then 2 * d a * d c * K (p c - p a) ^ 2 else 0 := by
    intro c
    by_cases hac : a < c
    · rw [if_pos hac]
      by_cases hcr : c ≤ a + r
      · have e1 : |(a : ℤ) - (c : ℤ)| ≤ (r : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
        have e2 : |(c : ℤ) - (a : ℤ)| ≤ (r : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
        have e3 : K (p a - p c) = K (p c - p a) := by
          rw [← hK (p c - p a)]
          congr 1
          ring
        rw [if_pos e1, if_pos e2, if_pos ⟨hac, by omega⟩, e3]
        ring
      · have e1 : ¬ |(a : ℤ) - (c : ℤ)| ≤ (r : ℤ) := fun h => by
          have := (abs_le.mp h).1
          omega
        have e2 : ¬ |(c : ℤ) - (a : ℤ)| ≤ (r : ℤ) := fun h => by
          have := (abs_le.mp h).2
          omega
        rw [if_neg e1, if_neg e2, if_neg (fun h => hcr (by omega)), add_zero]
    · rw [if_neg hac, if_neg (fun h => hac h.1)]
  have hset : (range n).filter (fun c => a + 1 ≤ c ∧ c < a + r + 1)
      = (Ico (a + 1) (a + r + 1)).filter (fun c => c < n) := by
    ext c
    simp only [mem_filter, mem_range, mem_Ico]
    tauto
  calc ∑ c ∈ range n,
        (if a < c then
          (fun a c : ℕ =>
              if |(a : ℤ) - (c : ℤ)| ≤ (r : ℤ) then d a * d c * K (p c - p a) ^ 2 else 0) a c
            + (fun a c : ℕ =>
              if |(a : ℤ) - (c : ℤ)| ≤ (r : ℤ) then d a * d c * K (p c - p a) ^ 2 else 0) c a
          else 0)
      = ∑ c ∈ range n,
          (if a + 1 ≤ c ∧ c < a + r + 1 then 2 * d a * d c * K (p c - p a) ^ 2 else 0) :=
        sum_congr rfl fun c _ => hpt c
    _ = ∑ c ∈ (range n).filter (fun c => a + 1 ≤ c ∧ c < a + r + 1),
          2 * d a * d c * K (p c - p a) ^ 2 := (sum_filter _ _).symm
    _ = ∑ c ∈ (Ico (a + 1) (a + r + 1)).filter (fun c => c < n),
          2 * d a * d c * K (p c - p a) ^ 2 := by rw [hset]
    _ = ∑ c ∈ Ico (a + 1) (a + r + 1),
          (if c < n then 2 * d a * d c * K (p c - p a) ^ 2 else 0) := sum_filter _ _
    _ = ∑ s ∈ range r,
          (if a + s + 1 < n then 2 * d a * d (a + s + 1) * K (p (a + s + 1) - p a) ^ 2
            else 0) := by
        rw [sum_Ico_eq_sum_range]
        have e : a + r + 1 - (a + 1) = r := by omega
        rw [e]
        refine sum_congr rfl fun s _ => ?_
        rw [show a + 1 + s = a + s + 1 by omega]

/-- The energy of a finite chain is at most the sum, over its points, of the energy of the pairs
formed with the next `r` points of the infinite sequence. -/
theorem chainEnergy_le_sum {K : ℝ → ℝ} (hK : ∀ t, K (-t) = K t) (r : ℕ) {d : ℕ → ℝ} (p : ℕ → ℝ)
    (hd : ∀ a, 0 ≤ d a) (n : ℕ) :
    chainEnergy K r d p n
      ≤ ∑ a ∈ range n, ∑ s ∈ range r,
          2 * d a * d (a + s + 1) * K (p (a + s + 1) - p a) ^ 2 := by
  rw [chainEnergy_eq_sum hK]
  refine sum_le_sum fun a _ => sum_le_sum fun s _ => ?_
  have hg : 0 ≤ 2 * d a * d (a + s + 1) * K (p (a + s + 1) - p a) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hd a)) (hd _)) (sq_nonneg _)
  split_ifs
  · exact le_rfl
  · exact hg

/-- **The energy of `M` periods is at most `M` times the energy per period.** -/
theorem chainEnergy_le_mul {K : ℝ → ℝ} (hK : ∀ t, K (-t) = K t) {m : ℕ} {P : ℝ} {d p : ℕ → ℝ}
    (hd0 : ∀ a, 0 ≤ d a) (hd : ∀ a, d (a + m) = d a) (hp : ∀ a, p (a + m) = p a + P)
    (r M : ℕ) :
    chainEnergy K r d p (M * m) ≤ M * periodEnergy K d p m r := by
  refine (chainEnergy_le_sum hK r p hd0 (M * m)).trans (le_of_eq ?_)
  unfold periodEnergy
  refine sum_range_mul_periodic _ m (fun a => ?_) M
  refine sum_congr rfl fun s _ => ?_
  have e1 : a + m + s + 1 = a + s + 1 + m := by omega
  have e2 : p (a + s + 1) + P - (p a + P) = p (a + s + 1) - p a := by ring
  rw [e1, hd a, hd (a + s + 1), hp a, hp (a + s + 1), e2]

/-! ## The limit `M → ∞` -/

/-- If `M A - C ≤ M e` for every natural number `M`, then `A ≤ e`. -/
theorem le_of_forall_nat_mul_sub_le {A e C : ℝ} (h : ∀ M : ℕ, (M : ℝ) * A - C ≤ M * e) :
    A ≤ e := by
  by_contra hlt
  have hpos : 0 < A - e := sub_pos.mpr (not_le.mp hlt)
  obtain ⟨M, hM⟩ := exists_nat_gt (C / (A - e))
  have h2 : C < M * (A - e) := (div_lt_iff₀ hpos).mp hM
  have h3 := h M
  rw [mul_sub] at h2
  linarith

/-- **Inequality (⋆), general form.** Let `p`, `d`, `ρ` be periodic (`m` points per period, period
`P`). If for every `M` the configuration of `M` periods satisfies
`∑ ρ - b M P - C₃ ≤ (energy of range r_M)`, and the energies per period of these ranges are at most
`e`, then `∑_{i < m} ρ_i - b P ≤ e`. -/
theorem star_core {K : ℝ → ℝ} (hK : ∀ t, K (-t) = K t) {m : ℕ} {P : ℝ} {d p ρ : ℕ → ℝ}
    (hd0 : ∀ a, 0 ≤ d a) (hd : ∀ a, d (a + m) = d a) (hp : ∀ a, p (a + m) = p a + P)
    (hρ : ∀ a, ρ (a + m) = ρ a) {b C₃ e : ℝ}
    (hcert : ∀ M : ℕ, ∃ r : ℕ,
      ∑ a ∈ range (M * m), ρ a - b * (M * P) - C₃ ≤ chainEnergy K r d p (M * m)
        ∧ periodEnergy K d p m r ≤ e) :
    ∑ i ∈ range m, ρ i - b * P ≤ e := by
  refine le_of_forall_nat_mul_sub_le (C := C₃) fun M => ?_
  obtain ⟨r, h1, h2⟩ := hcert M
  have h3 := chainEnergy_le_mul hK hd0 hd hp r M
  have h4 : (M : ℝ) * periodEnergy K d p m r ≤ M * e :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg M)
  rw [sum_range_mul_periodic ρ m hρ M] at h1
  have e1 : (M : ℝ) * (∑ i ∈ range m, ρ i - b * P) - C₃
      = (M : ℝ) * ∑ i ∈ range m, ρ i - b * (M * P) - C₃ := by ring
  rw [e1]
  linarith

/-! ## Separated periodic chains -/

/-- A sequence with nonnegative gaps is monotone. -/
theorem pos_mono {p : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hgap : ∀ a, θ ≤ p (a + 1) - p a) :
    Monotone p :=
  monotone_nat_of_le_succ fun a => by linarith [hgap a]

/-- Gaps at least `θ ≥ 0` give separation `θ` between any two points. -/
theorem sep_of_gap {p : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hgap : ∀ a, θ ≤ p (a + 1) - p a)
    {a c : ℕ} (h : a < c) : θ ≤ p c - p a := by
  have h1 : p (a + 1) ≤ p c := pos_mono hθ hgap h
  linarith [hgap a]

/-- The period is nonnegative. -/
theorem period_nonneg {p : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hgap : ∀ a, θ ≤ p (a + 1) - p a)
    {m : ℕ} {P : ℝ} (hp : ∀ a, p (a + m) = p a + P) : 0 ≤ P := by
  have h1 : p 0 ≤ p (0 + m) := pos_mono hθ hgap (Nat.zero_le _)
  rw [hp 0] at h1
  linarith

/-- The first `M m` points lie in an interval of length `M P`. -/
theorem span_le {p : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hgap : ∀ a, θ ≤ p (a + 1) - p a)
    {m : ℕ} {P : ℝ} (hp : ∀ a, p (a + m) = p a + P) {M a c : ℕ} (hc : c < M * m) :
    p c - p a ≤ M * P := by
  have h1 : p c ≤ p (0 + M * m) := pos_mono hθ hgap (by omega)
  have h2 : p 0 ≤ p a := pos_mono hθ hgap (Nat.zero_le _)
  rw [shift_add_mul p m P hp 0 M] at h1
  linarith

/-! ## From sums over `Fin n` to sums over `range n` -/

theorem sum_fin_fin_eq (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, F i j = ∑ a ∈ range n, ∑ c ∈ range n, F a c := by
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ c ∈ range n, F a c) n]
  exact sum_congr rfl fun i _ => Fin.sum_univ_eq_sum_range (fun c => F i c) n

/-- The pair energy of range `r` of `PairCertFor`, for a chain cut from sequences. -/
theorem sum_fin_range_energy (K : ℝ → ℝ) (r n : ℕ) (d p : ℕ → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
        if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ) then
          d i * d j * K (p j - p i) ^ 2 else 0)
      = chainEnergy K r d p n := by
  unfold chainEnergy
  rw [← sum_fin_fin_eq]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  exact if_congr (and_congr_left' Fin.val_ne_iff.symm) rfl rfl

/-- The pair energy of `PairCertAllFor`, for a chain of `n` points cut from sequences: all pairs
have index distance at most `n`. -/
theorem sum_fin_all_energy (K : ℝ → ℝ) (n : ℕ) (d p : ℕ → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then d i * d j * K (p j - p i) ^ 2 else 0)
      = chainEnergy K n d p n := by
  unfold chainEnergy
  rw [← sum_fin_fin_eq]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have hi := i.isLt
  have hj := j.isLt
  have habs : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (n : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
  exact if_congr ⟨fun h => ⟨Fin.val_ne_iff.mpr h, habs⟩, fun h => Fin.val_ne_iff.mp h.1⟩ rfl rfl

/-! ## Inequality (⋆) for the four kinds of certificates -/

section Star

variable {K : ℝ → ℝ} {θ : ℝ} {m : ℕ} {P : ℝ} {p : ℕ → ℝ}

/-- **Inequality (⋆), labelled points, range `r`.** For a periodic `θ`-separated configuration with
labels `L`, a certificate `(x₁, x₂, b)` of range `r` satisfies
`x₁ n₁ + x₂ n₂ - b P ≤ (pair energy per period, range r)`. -/
theorem PairCertFor.star (hK : ∀ t, K (-t) = K t) (hθ : 0 ≤ θ) {L : ℕ → Fin 2}
    (hp : ∀ a, p (a + m) = p a + P) (hL : ∀ a, L (a + m) = L a)
    (hgap : ∀ a, θ ≤ p (a + 1) - p a) {r : ℕ} {x₁ x₂ b : ℝ}
    (h : PairCertFor K θ r x₁ x₂ b) :
    ∑ i ∈ range m, (if L i = 0 then x₁ else x₂) - b * P
      ≤ periodEnergy K (fun a => mulOf (L a)) p m r := by
  obtain ⟨C₃, hC⟩ := h
  refine star_core hK (d := fun a => mulOf (L a)) (ρ := fun a => if L a = 0 then x₁ else x₂)
    (fun a => mulOf_nonneg _) (fun a => by simp only [hL]) hp (fun a => by simp only [hL])
    (C₃ := C₃) fun M => ⟨r, ?_, le_rfl⟩
  have key : ∑ i : Fin (M * m), (if L i = 0 then x₁ else x₂) - b * (M * P) - C₃
      ≤ ∑ i : Fin (M * m), ∑ j : Fin (M * m),
          if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ) then
            mulOf (L i) * mulOf (L j) * K (p j - p i) ^ 2 else 0 :=
    hC (M * m) (fun a => p a) (fun a => L a) (M * P)
      (fun i j hij => sep_of_gap hθ hgap hij)
      (mul_nonneg (Nat.cast_nonneg M) (period_nonneg hθ hgap hp))
      (fun i j => span_le hθ hgap hp j.isLt)
  have e1 : ∑ i : Fin (M * m), (if L i = 0 then x₁ else x₂)
      = ∑ a ∈ range (M * m), (if L a = 0 then x₁ else x₂) :=
    Fin.sum_univ_eq_sum_range (fun a => if L a = 0 then x₁ else x₂) (M * m)
  have e2 : (∑ i : Fin (M * m), ∑ j : Fin (M * m),
        if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ) then
          mulOf (L i) * mulOf (L j) * K (p j - p i) ^ 2 else 0)
      = chainEnergy K r (fun a => mulOf (L a)) p (M * m) :=
    sum_fin_range_energy K r (M * m) (fun a => mulOf (L a)) p
  rw [e1, e2] at key
  exact key

/-- **Inequality (⋆), labelled points, all pairs.** As `PairCertFor.star`, with any common upper
bound `e` for the pair energies per period of all ranges. -/
theorem PairCertAllFor.star (hK : ∀ t, K (-t) = K t) (hθ : 0 ≤ θ) {L : ℕ → Fin 2}
    (hp : ∀ a, p (a + m) = p a + P) (hL : ∀ a, L (a + m) = L a)
    (hgap : ∀ a, θ ≤ p (a + 1) - p a) {x₁ x₂ b : ℝ}
    (h : PairCertAllFor K θ x₁ x₂ b) {e : ℝ}
    (he : ∀ r, periodEnergy K (fun a => mulOf (L a)) p m r ≤ e) :
    ∑ i ∈ range m, (if L i = 0 then x₁ else x₂) - b * P ≤ e := by
  obtain ⟨C₃, hC⟩ := h
  refine star_core hK (d := fun a => mulOf (L a)) (ρ := fun a => if L a = 0 then x₁ else x₂)
    (fun a => mulOf_nonneg _) (fun a => by simp only [hL]) hp (fun a => by simp only [hL])
    (C₃ := C₃) fun M => ⟨M * m, ?_, he _⟩
  have key : ∑ i : Fin (M * m), (if L i = 0 then x₁ else x₂) - b * (M * P) - C₃
      ≤ ∑ i : Fin (M * m), ∑ j : Fin (M * m),
          if i ≠ j then mulOf (L i) * mulOf (L j) * K (p j - p i) ^ 2 else 0 :=
    hC (M * m) (fun a => p a) (fun a => L a) (M * P)
      (fun i j hij => sep_of_gap hθ hgap hij)
      (mul_nonneg (Nat.cast_nonneg M) (period_nonneg hθ hgap hp))
      (fun i j => span_le hθ hgap hp j.isLt)
  have e1 : ∑ i : Fin (M * m), (if L i = 0 then x₁ else x₂)
      = ∑ a ∈ range (M * m), (if L a = 0 then x₁ else x₂) :=
    Fin.sum_univ_eq_sum_range (fun a => if L a = 0 then x₁ else x₂) (M * m)
  have e2 : (∑ i : Fin (M * m), ∑ j : Fin (M * m),
        if i ≠ j then mulOf (L i) * mulOf (L j) * K (p j - p i) ^ 2 else 0)
      = chainEnergy K (M * m) (fun a => mulOf (L a)) p (M * m) :=
    sum_fin_all_energy K (M * m) (fun a => mulOf (L a)) p
  rw [e1, e2] at key
  exact key

/-- **Inequality (⋆), simple points, range `r`**: `x m - b P ≤ (pair energy per period)`. -/
theorem PairCert1For.star (hK : ∀ t, K (-t) = K t) (hθ : 0 ≤ θ)
    (hp : ∀ a, p (a + m) = p a + P) (hgap : ∀ a, θ ≤ p (a + 1) - p a) {r : ℕ} {x b : ℝ}
    (h : PairCert1For K θ r x b) :
    x * m - b * P ≤ periodEnergy K (fun _ => 1) p m r := by
  obtain ⟨C₃, hC⟩ := h
  have hmain : ∑ _i ∈ range m, x - b * P ≤ periodEnergy K (fun _ => 1) p m r := by
    refine star_core hK (d := fun _ => 1) (ρ := fun _ => x)
      (fun _ => zero_le_one) (fun _ => rfl) hp (fun _ => rfl) (C₃ := C₃) fun M => ⟨r, ?_, le_rfl⟩
    have key : x * ((M * m : ℕ) : ℝ) - b * (M * P) - C₃
        ≤ ∑ i : Fin (M * m), ∑ j : Fin (M * m),
            if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ) then
              K (p j - p i) ^ 2 else 0 :=
      hC (M * m) (fun a => p a) (M * P)
        (fun i j hij => sep_of_gap hθ hgap hij)
        (mul_nonneg (Nat.cast_nonneg M) (period_nonneg hθ hgap hp))
        (fun i j => span_le hθ hgap hp j.isLt)
    have e2 : (∑ i : Fin (M * m), ∑ j : Fin (M * m),
          if i ≠ j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ (r : ℤ) then
            K (p j - p i) ^ 2 else 0)
        = chainEnergy K r (fun _ => 1) p (M * m) := by
      rw [← sum_fin_range_energy]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      simp only [one_mul]
    rw [e2] at key
    rw [sum_const, card_range, nsmul_eq_mul]
    linarith
  rw [sum_const, card_range, nsmul_eq_mul] at hmain
  linarith

/-- **Inequality (⋆), simple points, all pairs.** -/
theorem PairCert1AllFor.star (hK : ∀ t, K (-t) = K t) (hθ : 0 ≤ θ)
    (hp : ∀ a, p (a + m) = p a + P) (hgap : ∀ a, θ ≤ p (a + 1) - p a) {x b : ℝ}
    (h : PairCert1AllFor K θ x b) {e : ℝ}
    (he : ∀ r, periodEnergy K (fun _ => 1) p m r ≤ e) :
    x * m - b * P ≤ e := by
  obtain ⟨C₃, hC⟩ := h
  have hmain : ∑ _i ∈ range m, x - b * P ≤ e := by
    refine star_core hK (d := fun _ => 1) (ρ := fun _ => x)
      (fun _ => zero_le_one) (fun _ => rfl) hp (fun _ => rfl) (C₃ := C₃)
      fun M => ⟨M * m, ?_, he _⟩
    have key : x * ((M * m : ℕ) : ℝ) - b * (M * P) - C₃
        ≤ ∑ i : Fin (M * m), ∑ j : Fin (M * m), if i ≠ j then K (p j - p i) ^ 2 else 0 :=
      hC (M * m) (fun a => p a) (M * P)
        (fun i j hij => sep_of_gap hθ hgap hij)
        (mul_nonneg (Nat.cast_nonneg M) (period_nonneg hθ hgap hp))
        (fun i j => span_le hθ hgap hp j.isLt)
    have e2 : (∑ i : Fin (M * m), ∑ j : Fin (M * m), if i ≠ j then K (p j - p i) ^ 2 else 0)
        = chainEnergy K (M * m) (fun _ => 1) p (M * m) := by
      rw [← sum_fin_all_energy]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      simp only [one_mul]
    rw [e2] at key
    rw [sum_const, card_range, nsmul_eq_mul]
    linarith
  rw [sum_const, card_range, nsmul_eq_mul] at hmain
  linarith

end Star

/-! ## All pairs: regrouping by periods -/

/-- The indices `i + 1, …, i + r` (with `i < m`) lie among the indices `i' > i` of the first
period and the indices `i' + n m` of the periods `n = 1, …, r`. -/
theorem sum_shift_le_period_sum {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) {m i : ℕ} (hi : i < m) (r : ℕ) :
    ∑ s ∈ range r, f (i + s + 1)
      ≤ ∑ i' ∈ range m, (if i < i' then f i' else 0)
        + ∑ i' ∈ range m, ∑ n ∈ range r, f (i' + (n + 1) * m) := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ j, g j = if i < j then f j else 0 := ⟨_, fun _ => rfl⟩
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    rw [hg]
    split_ifs
    · exact hf j
    · exact le_rfl
  have h1 : ∑ s ∈ range r, f (i + s + 1) = ∑ s ∈ range r, g (i + 1 + s) :=
    sum_congr rfl fun s _ => by
      rw [hg, if_pos (by omega), show i + 1 + s = i + s + 1 by omega]
  have hle : i + 1 + r ≤ (r + 1) * m := by
    have h : r ≤ r * m := Nat.le_mul_of_pos_right r (by omega)
    rw [add_mul, one_mul]
    omega
  have h2 : ∑ s ∈ range r, g (i + 1 + s) ≤ ∑ j ∈ range ((r + 1) * m), g j :=
    calc ∑ s ∈ range r, g (i + 1 + s)
        ≤ ∑ j ∈ range (i + 1), g j + ∑ s ∈ range r, g (i + 1 + s) :=
          le_add_of_nonneg_left (sum_nonneg fun j _ => hg0 j)
      _ = ∑ j ∈ range (i + 1 + r), g j := (sum_range_add g (i + 1) r).symm
      _ ≤ ∑ j ∈ range ((r + 1) * m), g j :=
          sum_le_sum_of_subset_of_nonneg (range_mono hle) fun j _ _ => hg0 j
  have h3 : ∑ j ∈ range ((r + 1) * m), g j
      = ∑ u ∈ range r, ∑ i' ∈ range m, g ((u + 1) * m + i') + ∑ i' ∈ range m, g (0 * m + i') := by
    rw [sum_range_mul, sum_range_succ']
  have h4 : ∑ u ∈ range r, ∑ i' ∈ range m, g ((u + 1) * m + i')
      = ∑ i' ∈ range m, ∑ n ∈ range r, f (i' + (n + 1) * m) := by
    rw [sum_comm]
    refine sum_congr rfl fun i' _ => sum_congr rfl fun n _ => ?_
    have h : m ≤ (n + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    rw [hg, if_pos (by omega), add_comm]
  have h5 : ∑ i' ∈ range m, g (0 * m + i') = ∑ i' ∈ range m, (if i < i' then f i' else 0) :=
    sum_congr rfl fun i' _ => by rw [zero_mul, zero_add, hg]
  linarith

/-- **The energy per period, all ranges at once.** If `T i i'` bounds the sums
`∑_{n=1}^{r} K(p_{i'} - p_i + n P)²` for all `r`, then for every range `r`
`periodEnergy K d p m r ≤ ∑_{i, i' < m} 2 d_i d_{i'} ([i < i'] K(p_{i'} - p_i)² + T i i')`. -/
theorem periodEnergy_le_all {K : ℝ → ℝ} {m : ℕ} {P : ℝ} {d p : ℕ → ℝ} (hd0 : ∀ a, 0 ≤ d a)
    (hd : ∀ a, d (a + m) = d a) (hp : ∀ a, p (a + m) = p a + P) (T : ℕ → ℕ → ℝ)
    (hT : ∀ i < m, ∀ i' < m, ∀ r : ℕ,
      ∑ n ∈ range r, K (p i' - p i + ((n : ℝ) + 1) * P) ^ 2 ≤ T i i') (r : ℕ) :
    periodEnergy K d p m r
      ≤ ∑ i ∈ range m, ∑ i' ∈ range m,
          2 * d i * d i' * ((if i < i' then K (p i' - p i) ^ 2 else 0) + T i i') := by
  unfold periodEnergy
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.mp hi
  have hf : ∀ j, 0 ≤ 2 * d i * d j * K (p j - p i) ^ 2 := fun j =>
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hd0 i)) (hd0 j)) (sq_nonneg _)
  have h1 : ∑ s ∈ range r, 2 * d i * d (i + s + 1) * K (p (i + s + 1) - p i) ^ 2
      ≤ ∑ i' ∈ range m, (if i < i' then 2 * d i * d i' * K (p i' - p i) ^ 2 else 0)
        + ∑ i' ∈ range m, ∑ n ∈ range r,
            2 * d i * d (i' + (n + 1) * m) * K (p (i' + (n + 1) * m) - p i) ^ 2 :=
    sum_shift_le_period_sum (f := fun j => 2 * d i * d j * K (p j - p i) ^ 2) hf hi' r
  refine h1.trans ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun i' hi2 => ?_
  have hi2' := mem_range.mp hi2
  have hper : ∀ n : ℕ,
      2 * d i * d (i' + (n + 1) * m) * K (p (i' + (n + 1) * m) - p i) ^ 2
        = 2 * d i * d i' * K (p i' - p i + ((n : ℝ) + 1) * P) ^ 2 := by
    intro n
    have e : p i' + ((n + 1 : ℕ) : ℝ) * P - p i = p i' - p i + ((n : ℝ) + 1) * P := by
      push_cast
      ring
    rw [periodic_add_mul d m hd, shift_add_mul p m P hp, e]
  have hsum : ∑ n ∈ range r,
        2 * d i * d (i' + (n + 1) * m) * K (p (i' + (n + 1) * m) - p i) ^ 2
      ≤ 2 * d i * d i' * T i i' := by
    rw [sum_congr rfl fun n _ => hper n, ← mul_sum]
    exact mul_le_mul_of_nonneg_left (hT i hi' i' hi2' r)
      (mul_nonneg (mul_nonneg (by norm_num) (hd0 i)) (hd0 i'))
  have hsplit : 2 * d i * d i' * ((if i < i' then K (p i' - p i) ^ 2 else 0) + T i i')
      = (if i < i' then 2 * d i * d i' * K (p i' - p i) ^ 2 else 0) + 2 * d i * d i' * T i i' := by
    rw [mul_add, mul_ite, mul_zero]
  rw [hsplit]
  exact add_le_add le_rfl hsum

end Ceilings
