import Sude.GeneratedTwinScan.S078C00
import Sude.GeneratedTwinScan.S078C01
import Sude.GeneratedTwinScan.S078C02
import Sude.GeneratedTwinScan.S078C03
import Sude.GeneratedTwinScan.S078C04
import Sude.GeneratedTwinScan.S078C05
import Sude.GeneratedTwinScan.S078C06
import Sude.GeneratedTwinScan.S078C07
import Sude.GeneratedTwinScan.S078C08
import Sude.GeneratedTwinScan.S078C09
import Sude.GeneratedTwinScan.S078C10
import Sude.GeneratedTwinScan.S078C11
import Sude.GeneratedTwinScan.S078C12
import Sude.GeneratedTwinScan.S078C13
import Sude.GeneratedTwinScan.S078C14
import Sude.GeneratedTwinScan.S078C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S078All

theorem join_0_0 : (twinPrimeSegment 163577901 163840045).card = 957 := by
  simpa using combineTwinPrimeSegments (by decide : 163577901 ≤ 163708973)
    (by decide : 163708973 ≤ 163840045) S078C00.total S078C01.total

theorem join_0_1 : (twinPrimeSegment 163840045 164102189).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 163840045 ≤ 163971117)
    (by decide : 163971117 ≤ 164102189) S078C02.total S078C03.total

theorem join_0_2 : (twinPrimeSegment 164102189 164364333).card = 990 := by
  simpa using combineTwinPrimeSegments (by decide : 164102189 ≤ 164233261)
    (by decide : 164233261 ≤ 164364333) S078C04.total S078C05.total

theorem join_0_3 : (twinPrimeSegment 164364333 164626477).card = 977 := by
  simpa using combineTwinPrimeSegments (by decide : 164364333 ≤ 164495405)
    (by decide : 164495405 ≤ 164626477) S078C06.total S078C07.total

theorem join_0_4 : (twinPrimeSegment 164626477 164888621).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 164626477 ≤ 164757549)
    (by decide : 164757549 ≤ 164888621) S078C08.total S078C09.total

theorem join_0_5 : (twinPrimeSegment 164888621 165150765).card = 928 := by
  simpa using combineTwinPrimeSegments (by decide : 164888621 ≤ 165019693)
    (by decide : 165019693 ≤ 165150765) S078C10.total S078C11.total

theorem join_0_6 : (twinPrimeSegment 165150765 165412909).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 165150765 ≤ 165281837)
    (by decide : 165281837 ≤ 165412909) S078C12.total S078C13.total

theorem join_0_7 : (twinPrimeSegment 165412909 165675053).card = 990 := by
  simpa using combineTwinPrimeSegments (by decide : 165412909 ≤ 165543981)
    (by decide : 165543981 ≤ 165675053) S078C14.total S078C15.total

theorem join_1_0 : (twinPrimeSegment 163577901 164102189).card = 1890 := by
  simpa using combineTwinPrimeSegments (by decide : 163577901 ≤ 163840045)
    (by decide : 163840045 ≤ 164102189) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 164102189 164626477).card = 1967 := by
  simpa using combineTwinPrimeSegments (by decide : 164102189 ≤ 164364333)
    (by decide : 164364333 ≤ 164626477) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 164626477 165150765).card = 1870 := by
  simpa using combineTwinPrimeSegments (by decide : 164626477 ≤ 164888621)
    (by decide : 164888621 ≤ 165150765) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 165150765 165675053).card = 1965 := by
  simpa using combineTwinPrimeSegments (by decide : 165150765 ≤ 165412909)
    (by decide : 165412909 ≤ 165675053) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 163577901 164626477).card = 3857 := by
  simpa using combineTwinPrimeSegments (by decide : 163577901 ≤ 164102189)
    (by decide : 164102189 ≤ 164626477) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 164626477 165675053).card = 3835 := by
  simpa using combineTwinPrimeSegments (by decide : 164626477 ≤ 165150765)
    (by decide : 165150765 ≤ 165675053) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 163577901 165675053).card = 7692 := by
  simpa using combineTwinPrimeSegments (by decide : 163577901 ≤ 164626477)
    (by decide : 164626477 ≤ 165675053) join_2_0 join_2_1

theorem total : (twinPrimeSegment 163577901 165675053).card = 7692 := join_3_0

end S078All
end Sude.GeneratedTwinScan
