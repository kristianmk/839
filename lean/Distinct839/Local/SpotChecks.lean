/-
Distinct839/Local/SpotChecks.lean — four small boxes of the domain, checked by the kernel.

These theorems are not used by the proof. The complete check of the local inequality
(`Distinct839/Local/RunAll.lean`) is evaluated by compiled code. Here the Lean kernel itself
evaluates the range-minimum test of the checker on four boxes of side `4/16384`, chosen by
hand (they are not boxes of the branch and bound, which stops at larger boxes), reading the
kernel table as the function `kTab`; `basicF_sound` and `kTab_sound` turn each evaluation into
the statement that the local inequality holds on the box, for all `128` labellings. The
theorems depend on the standard axioms only.

The boxes (gaps in units of `1/16384`):
* `spot_lattice`: all gaps near `1.0248`, where the slack of the inequality is smallest;
* `spot_double`: all gaps near `1.947`;
* `spot_corner`: all gaps at the lower end `13926/16384 < 17/20` of the root box;
* `spot_vacancy`: five gaps near `1.02`–`1.04` and one near `1.857`.
-/
import Distinct839.Local.Spot

namespace Distinct839.Local

theorem spot_lattice : BoxOK #[16790, 16790, 16790, 16790, 16790, 16790]
    #[16794, 16794, 16794, 16794, 16794, 16794] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

theorem spot_double : BoxOK #[31900, 31900, 31900, 31900, 31900, 31900]
    #[31904, 31904, 31904, 31904, 31904, 31904] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

theorem spot_corner : BoxOK #[13926, 13926, 13926, 13926, 13926, 13926]
    #[13930, 13930, 13930, 13930, 13930, 13930] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

theorem spot_vacancy : BoxOK #[17039, 16733, 16723, 16733, 17039, 30419]
    #[17043, 16737, 16727, 16737, 17043, 30423] :=
  basicF_sound kTab kTab_sound _ _ (by decide +kernel)

end Distinct839.Local
