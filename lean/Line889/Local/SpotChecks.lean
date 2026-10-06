/-
Line889/Local/SpotChecks.lean — four small boxes of the domain, checked by the kernel.

These theorems are not used by the proof. The complete check of the local inequality
(`Line889/Local/RunAll.lean`) is evaluated by compiled code. Here the Lean kernel itself
evaluates the range-minimum test of the checker on four small boxes, chosen by hand (they are
not boxes of the branch and bound), reading the kernel table as the function `kTab`;
`basicF_sound` and `kTab_sound` turn each evaluation into the statement that the local
inequality holds on the box (`BoxOK`, the scaled inequality in the format of the checker). The
theorems depend on the standard axioms only.

The boxes (gaps in units of `1/16384`). "Slack" is the right side minus the left side of the
local inequality; the values at points are floating-point evaluations and serve only to choose
the boxes. "Margin" is the exact value by which the range-minimum test passes on the box, in
the same units.

* `spot_corner`: side `4`, all gaps at the lower end `13926/16384 < 17/20` of the root box.
  Margin `0.16`.
* `spot_lattice`: side `4`, around the unit lattice (all gaps `1`), where the slack is
  `3.0 · 10⁻³`. Margin `2.9 · 10⁻³`.
* `spot_tightest`: side `1`, around the point with the smallest slack that a floating-point
  search found (local minimisation from about 2850 starting points): gaps
  `2.125, 1.15651, 1.625, 1.16011, 1.05033, 2.125`, slack `1.04 · 10⁻⁵`. Its first, third and
  last gap are at knots `3/4 + k/8` of the piecewise linear potentials. Margin `1.2 · 10⁻⁶`.
  The side is `1`: on every box of side `2` or `4` with integer corners that contains this
  point the range-minimum test fails, because on such a box it loses more than the slack.
* `spot_second`: side `1`, around the point with the second smallest slack found: gaps
  `2.125, 2.82085, 1.06286, 1.03941, 1.03344, 1.03466`, slack `2.0 · 10⁻⁵`. Margin
  `9.3 · 10⁻⁶`. Here too the test fails on the boxes of side `2` and `4` that contain the
  point.
-/
import Line889.Local.Spot

namespace Line889.Local

theorem spot_corner : BoxOK #[13926, 13926, 13926, 13926, 13926, 13926]
    #[13930, 13930, 13930, 13930, 13930, 13930] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

theorem spot_lattice : BoxOK #[16384, 16380, 16380, 16380, 16380, 16384]
    #[16388, 16384, 16384, 16384, 16384, 16388] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

theorem spot_tightest : BoxOK #[34816, 18948, 26623, 19007, 17208, 34816]
    #[34817, 18949, 26624, 19008, 17209, 34817] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

theorem spot_second : BoxOK #[34816, 46216, 17413, 17029, 16931, 16951]
    #[34817, 46217, 17414, 17030, 16932, 16952] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

end Line889.Local
