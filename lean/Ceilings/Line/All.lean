/-
Ceilings/Line/All.lean — second window: no pair-energy certificate gives more than 67.383%.

`ceiling_line_all`: for the window of `Simple673`, every pair-energy certificate `(x, b)` for
simple points and all pairs, with `x < 1`, has `(2 - C - b)/(1 - x) < 0.67383`. By
`PairCert1.toAll` this covers the certificates of every range (`ceiling_line_any_range`). The
hypothesis `0 ≤ b` of the statement is not used.

Two periodic trial states of simple points with integer periods: two points in a period of length
`3` with gaps `1.03846`, `1.96154`; and five points in a period of length `7` with gaps `1.03009`,
`1.03009`, `1.95116`, `1.03749`, `1.95117`. For each state the pair energy per period of every
range is bounded by `eUp` (`State.allUp`, with `N₀ = 60` periods and the tail from `T₀ = 180` on
for the first state, `N₀ = 30` and `T₀ = 210` for the second; the distances between a point and
its own translates are integers, and the kernel does not vanish at `3`, `6`, `9` for the first
state and at `7` for the second). The mixture with the weights `weights` has `0.6738216857…`
points per unit length.
-/
import Ceilings.Line.Kernel

namespace Ceilings

namespace Line.All

/-- The two trial states, of periods three and seven. -/
def states : Fin 2 → State := ![
  ⟨[1, 1], [51923 / 50000, 98077 / 50000]⟩,
  ⟨[1, 1, 1, 1, 1],
    [103009 / 100000, 103009 / 100000, 48779 / 25000, 103749 / 100000, 195117 / 100000]⟩]

/-- The weights of the mixture (not normalised). -/
def weights : Fin 2 → ℚ := ![283248199915, 21465057180]

/-- Upper bounds for the pair energies per period, all pairs. -/
def eUp : Fin 2 → ℚ := ![2536320267 / 500000000000, 1547362617 / 100000000000]

/-- number of periods evaluated explicitly -/
def N₀ : Fin 2 → ℕ := ![60, 30]

/-- the tail bound `Q(t)² ≤ E²/t²` is used for `t ≥ T₀ = N₀ · P` -/
def T₀ : Fin 2 → ℚ := ![180, 210]

theorem sep_ok : ∀ k, (states k).sepOK (17 / 20) = true := by decide +kernel

theorem simple_ok : ∀ k, (states k).simpleOK = true := by decide +kernel

theorem T_ok : ∀ k, 10 < T₀ k := by decide +kernel

theorem all_ok : ∀ k, (states k).allOK (T₀ k) (N₀ k) = true := by decide +kernel

theorem energy_ok : ∀ k, (states k).allUp Q kI (E2gen aQ (T₀ k)) (N₀ k) ≤ eUp k := by
  decide +kernel

theorem mix_ok : LineMixOK states weights eUp CloLineQ := by decide +kernel

theorem ratio_lt : mixM states weights / mixP states weights < 67383 / 100000 := by
  decide +kernel

end Line.All

open Line.All in
/-- **Ceiling for all pair-energy certificates, simple points** (window of `Simple673`): the
constant of a pair-energy certificate is below `0.67383`. -/
theorem ceiling_line_all {x b : ℝ} (h : PairCert1All x b) (_hb : 0 ≤ b) (hx : x < 1) :
    (2 - energyCLine - b) / (1 - x) < 67383 / 100000 := by
  have h1 := Line.ceiling_of_all states weights eUp T₀ N₀ sep_ok simple_ok T_ok all_ok energy_ok
    mix_ok h hx
  have h2 : ((mixM states weights / mixP states weights : ℚ) : ℝ) < ((67383 / 100000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr ratio_lt
  have h3 : ((67383 / 100000 : ℚ) : ℝ) = 67383 / 100000 := by norm_num
  rw [h3] at h2
  exact lt_of_le_of_lt h1 h2

/-- With the second window no pair-energy certificate of any range gives more than `67.383%`. -/
theorem ceiling_line_any_range {r : ℕ} {x b : ℝ} (h : PairCert1 r x b) (hb : 0 ≤ b)
    (hx : x < 1) : (2 - energyCLine - b) / (1 - x) < 67383 / 100000 :=
  ceiling_line_all h.toAll hb hx

end Ceilings
