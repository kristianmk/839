/-
Distinct839/Kernel/Table.lean — the kernel table as an array, for the local-inequality checker.

`kTabArray` holds `kTab k` for `k = 0, …, tabR`. It computes the 8192 trigonometric enclosures once
(`trigArr`) and shares them between the 25 periods of the table, so that the compiled evaluation
of the whole array takes well under a minute. The three names `kTabArray`, `kTabArray_size` and
`kTabArray_sound` are the interface used by `Distinct839/Local`.
-/
import Distinct839.Kernel.Sound

namespace Distinct839.Kernel

/-- The 8192 enclosures `trigEncl j`, `j < H/2`, computed once. -/
def trigArr : Array TrigEncl := Array.ofFn (n := 8192) fun j => trigEncl j

/-- `trigEncl j`, read from `trigArr` when `j` is in range. -/
def trigCached (j : ℕ) : TrigEncl := if h : j < trigArr.size then trigArr[j] else trigEncl j

lemma trigCached_eq (j : ℕ) : trigCached j = trigEncl j := by
  unfold trigCached
  split_ifs with h
  · simp [trigArr]
  · rfl

/-- **The kernel table as an array**: `kTabArray[k] = kTab k` for `k ≤ tabR = 209009`. -/
def _root_.Distinct839.kTabArray : Array ℕ :=
  Array.ofFn (n := tabR + 1) fun k => kTabWith trigCached k

/-- The table has `tabR + 1 = 209010` entries. -/
theorem _root_.Distinct839.kTabArray_size : kTabArray.size = tabR + 1 := Array.size_ofFn

lemma kTabArray_getElem (k : ℕ) (h : k < kTabArray.size) : kTabArray[k] = kTab k := by
  have e : (trigCached : ℕ → TrigEncl) = trigEncl := funext trigCached_eq
  rw [kTab, ← e]
  exact Array.getElem_ofFn _

/-- **Soundness of the array**: `kTabArray[k] / 2²⁸ ≤ K(t)²` on `[k/16384, (k+1)/16384]`. -/
theorem _root_.Distinct839.kTabArray_sound : ∀ (k : ℕ) (h : k < kTabArray.size) (t : ℝ),
    (k : ℝ) / gridH ≤ t → t ≤ ((k : ℝ) + 1) / gridH → (kTabArray[k] : ℝ) / scaleV ≤ K t ^ 2 := by
  intro k h t h1 h2
  rw [kTabArray_getElem]
  exact kTab_sound k t h1 h2

end Distinct839.Kernel
