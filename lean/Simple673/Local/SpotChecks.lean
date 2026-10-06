/-
Simple673/Local/SpotChecks.lean — four small boxes of the domain, checked by the kernel.

These theorems are not used by the proof. The complete check of the local inequality
(`Simple673/Local/RunAll.lean`) is evaluated by compiled code. Here the Lean kernel itself
evaluates the range-minimum test of the checker on four small boxes, chosen by hand (they are
not boxes of the branch and bound), reading the kernel table as the function `kTab`;
`basicF_sound` and `kTab_sound` turn each evaluation into the statement that the local
inequality holds on the box (`BoxOK`, the scaled inequality in the format of the checker). The
theorems depend on the standard axioms only.

The boxes (seven gaps, in units of `1/16384`). "Slack" is the right side minus the left side of
the local inequality; the values at points are floating-point evaluations and serve only to
choose the boxes. "Margin" is the exact value by which the range-minimum test passes on the
box, in the same units.

* `spot_trial`: side `2`, around a frame of the first trial state of the ceiling for frames of
  eight points, with gaps `1.03627, 1.03627, 1.96582, 1.04317, 1.96582, 1.03627, 1.03627`,
  where the slack is `1.9 · 10⁻⁵`. Margin `7.6 · 10⁻⁶`.
* `spot_second_trial`: side `2`, around a frame of the second trial state, with gaps
  `1.04588, 1.97681, 1.04588, 1.98634, 1.98634, 1.04588, 1.97681`, where the slack is
  `1.7 · 10⁻⁵`. Margin `9.4 · 10⁻⁶`.
* `spot_corner`: side `4`, all gaps at the lower end `13926/16384 < 17/20` of the root box.
  Margin `0.17`.
* `spot_tightest`: side `2`, around the point with the smallest slack that a floating-point
  search found (local minimisation from the `2187` patterns of gaps near `1.04`, `1.97` and
  `2.92` and from random frames): gaps
  `1.03274, 1.03746, 1.96608, 1.04485, 1.96608, 1.03746, 1.03274`, slack `1.3 · 10⁻⁵`. Margin
  `8.4 · 10⁻⁷`.
-/
import Simple673.Local.Spot

namespace Simple673.Local

theorem spot_trial : BoxOK #[16978, 16977, 32206, 17090, 32206, 16977, 16978]
    #[16980, 16979, 32208, 17092, 32208, 16979, 16980] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

theorem spot_second_trial : BoxOK #[17135, 32388, 17134, 32543, 32543, 17134, 32387]
    #[17137, 32390, 17136, 32545, 32545, 17136, 32389] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

theorem spot_corner : BoxOK #[13926, 13926, 13926, 13926, 13926, 13926, 13926]
    #[13930, 13930, 13930, 13930, 13930, 13930, 13930] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

theorem spot_tightest : BoxOK #[16919, 16997, 32212, 17118, 32212, 16997, 16920]
    #[16921, 16999, 32214, 17120, 32214, 16999, 16922] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

end Simple673.Local
