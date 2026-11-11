import Sude.GeneratedTwinScan.S195C00
import Sude.GeneratedTwinScan.S195C01
import Sude.GeneratedTwinScan.S195C02
import Sude.GeneratedTwinScan.S195C03
import Sude.GeneratedTwinScan.S195C04
import Sude.GeneratedTwinScan.S195C05
import Sude.GeneratedTwinScan.S195C06
import Sude.GeneratedTwinScan.S195C07
import Sude.GeneratedTwinScan.S195C08
import Sude.GeneratedTwinScan.S195C09
import Sude.GeneratedTwinScan.S195C10
import Sude.GeneratedTwinScan.S195C11
import Sude.GeneratedTwinScan.S195C12
import Sude.GeneratedTwinScan.S195C13
import Sude.GeneratedTwinScan.S195C14
import Sude.GeneratedTwinScan.S195C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S195All

theorem join_0_0 : (twinPrimeSegment 408944685 409206829).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 408944685 ≤ 409075757)
    (by decide : 409075757 ≤ 409206829) S195C00.total S195C01.total

theorem join_0_1 : (twinPrimeSegment 409206829 409468973).card = 836 := by
  simpa using combineTwinPrimeSegments (by decide : 409206829 ≤ 409337901)
    (by decide : 409337901 ≤ 409468973) S195C02.total S195C03.total

theorem join_0_2 : (twinPrimeSegment 409468973 409731117).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 409468973 ≤ 409600045)
    (by decide : 409600045 ≤ 409731117) S195C04.total S195C05.total

theorem join_0_3 : (twinPrimeSegment 409731117 409993261).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 409731117 ≤ 409862189)
    (by decide : 409862189 ≤ 409993261) S195C06.total S195C07.total

theorem join_0_4 : (twinPrimeSegment 409993261 410255405).card = 886 := by
  simpa using combineTwinPrimeSegments (by decide : 409993261 ≤ 410124333)
    (by decide : 410124333 ≤ 410255405) S195C08.total S195C09.total

theorem join_0_5 : (twinPrimeSegment 410255405 410517549).card = 844 := by
  simpa using combineTwinPrimeSegments (by decide : 410255405 ≤ 410386477)
    (by decide : 410386477 ≤ 410517549) S195C10.total S195C11.total

theorem join_0_6 : (twinPrimeSegment 410517549 410779693).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 410517549 ≤ 410648621)
    (by decide : 410648621 ≤ 410779693) S195C12.total S195C13.total

theorem join_0_7 : (twinPrimeSegment 410779693 411041837).card = 907 := by
  simpa using combineTwinPrimeSegments (by decide : 410779693 ≤ 410910765)
    (by decide : 410910765 ≤ 411041837) S195C14.total S195C15.total

theorem join_1_0 : (twinPrimeSegment 408944685 409468973).card = 1734 := by
  simpa using combineTwinPrimeSegments (by decide : 408944685 ≤ 409206829)
    (by decide : 409206829 ≤ 409468973) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 409468973 409993261).card = 1766 := by
  simpa using combineTwinPrimeSegments (by decide : 409468973 ≤ 409731117)
    (by decide : 409731117 ≤ 409993261) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 409993261 410517549).card = 1730 := by
  simpa using combineTwinPrimeSegments (by decide : 409993261 ≤ 410255405)
    (by decide : 410255405 ≤ 410517549) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 410517549 411041837).card = 1786 := by
  simpa using combineTwinPrimeSegments (by decide : 410517549 ≤ 410779693)
    (by decide : 410779693 ≤ 411041837) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 408944685 409993261).card = 3500 := by
  simpa using combineTwinPrimeSegments (by decide : 408944685 ≤ 409468973)
    (by decide : 409468973 ≤ 409993261) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 409993261 411041837).card = 3516 := by
  simpa using combineTwinPrimeSegments (by decide : 409993261 ≤ 410517549)
    (by decide : 410517549 ≤ 411041837) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 408944685 411041837).card = 7016 := by
  simpa using combineTwinPrimeSegments (by decide : 408944685 ≤ 409993261)
    (by decide : 409993261 ≤ 411041837) join_2_0 join_2_1

theorem total : (twinPrimeSegment 408944685 411041837).card = 7016 := join_3_0

end S195All
end Sude.GeneratedTwinScan
