/-
Line889/Kernel/Table.lean — the array of the kernel table agrees with the table and is sound.

`kTabArray` (`Line889/Kernel/Array.lean`) holds `kTab k` for `k = 0, …, tabR` (262144 entries,
16 periods), computed with the 8192 trigonometric enclosures shared between the periods. This
file proves that the shared enclosures are those of the definition of `kTab` (`trigCached_eq`),
hence `kTabArray[k] = kTab k` (`kTabArray_getElem`), and with `kTab_sound`
(`Line889/Kernel/Sound.lean`) that the array is a sound lower enclosure of `K²`
(`kTabArray_sound`). The three names `kTabArray`, `kTabArray_size` and `kTabArray_sound` are the
interface used by `Line889/Local`.

The definitions are kept in a file of their own, without proofs, because the compiled run of the
checker imports them: this file and the proofs behind it can change without a new run.
-/
import Line889.Kernel.Array
import Line889.Kernel.Sound

namespace Line889.Kernel

/-- The cached enclosure is the enclosure of the definition of `kTab`. -/
lemma trigCached_eq (j : ℕ) : trigCached j = Distinct839.Kernel.trigEncl j := by
  unfold trigCached
  split_ifs with h
  · simp [trigArr]
  · rfl

/-- The array holds the table: `kTabArray[k] = kTab k` for `k ≤ tabR`. -/
lemma kTabArray_getElem (k : ℕ) (h : k < kTabArray.size) : kTabArray[k] = kTab k := by
  have e : (trigCached : ℕ → Distinct839.Kernel.TrigEncl) = Distinct839.Kernel.trigEncl :=
    funext trigCached_eq
  rw [kTab, ← e]
  exact Array.getElem_ofFn _

/-- **Soundness of the array**: `kTabArray[k] / 2²⁸ ≤ K(t)²` on `[k/16384, (k+1)/16384]`. -/
theorem _root_.Line889.kTabArray_sound : ∀ (k : ℕ) (h : k < kTabArray.size) (t : ℝ),
    (k : ℝ) / gridH ≤ t → t ≤ ((k : ℝ) + 1) / gridH → (kTabArray[k] : ℝ) / scaleV ≤ K t ^ 2 := by
  intro k h t h1 h2
  rw [kTabArray_getElem]
  exact kTab_sound k t h1 h2

end Line889.Kernel
