import Sude.GeneratedTwinScan.S117C00
import Sude.GeneratedTwinScan.S117C01
import Sude.GeneratedTwinScan.S117C02
import Sude.GeneratedTwinScan.S117C03
import Sude.GeneratedTwinScan.S117C04
import Sude.GeneratedTwinScan.S117C05
import Sude.GeneratedTwinScan.S117C06
import Sude.GeneratedTwinScan.S117C07
import Sude.GeneratedTwinScan.S117C08
import Sude.GeneratedTwinScan.S117C09
import Sude.GeneratedTwinScan.S117C10
import Sude.GeneratedTwinScan.S117C11
import Sude.GeneratedTwinScan.S117C12
import Sude.GeneratedTwinScan.S117C13
import Sude.GeneratedTwinScan.S117C14
import Sude.GeneratedTwinScan.S117C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S117All

theorem join_0_0 : (twinPrimeSegment 245366829 245628973).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 245366829 ≤ 245497901)
    (by decide : 245497901 ≤ 245628973) S117C00.total S117C01.total

theorem join_0_1 : (twinPrimeSegment 245628973 245891117).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 245628973 ≤ 245760045)
    (by decide : 245760045 ≤ 245891117) S117C02.total S117C03.total

theorem join_0_2 : (twinPrimeSegment 245891117 246153261).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 245891117 ≤ 246022189)
    (by decide : 246022189 ≤ 246153261) S117C04.total S117C05.total

theorem join_0_3 : (twinPrimeSegment 246153261 246415405).card = 930 := by
  simpa using combineTwinPrimeSegments (by decide : 246153261 ≤ 246284333)
    (by decide : 246284333 ≤ 246415405) S117C06.total S117C07.total

theorem join_0_4 : (twinPrimeSegment 246415405 246677549).card = 962 := by
  simpa using combineTwinPrimeSegments (by decide : 246415405 ≤ 246546477)
    (by decide : 246546477 ≤ 246677549) S117C08.total S117C09.total

theorem join_0_5 : (twinPrimeSegment 246677549 246939693).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 246677549 ≤ 246808621)
    (by decide : 246808621 ≤ 246939693) S117C10.total S117C11.total

theorem join_0_6 : (twinPrimeSegment 246939693 247201837).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 246939693 ≤ 247070765)
    (by decide : 247070765 ≤ 247201837) S117C12.total S117C13.total

theorem join_0_7 : (twinPrimeSegment 247201837 247463981).card = 927 := by
  simpa using combineTwinPrimeSegments (by decide : 247201837 ≤ 247332909)
    (by decide : 247332909 ≤ 247463981) S117C14.total S117C15.total

theorem join_1_0 : (twinPrimeSegment 245366829 245891117).card = 1788 := by
  simpa using combineTwinPrimeSegments (by decide : 245366829 ≤ 245628973)
    (by decide : 245628973 ≤ 245891117) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 245891117 246415405).card = 1832 := by
  simpa using combineTwinPrimeSegments (by decide : 245891117 ≤ 246153261)
    (by decide : 246153261 ≤ 246415405) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 246415405 246939693).card = 1855 := by
  simpa using combineTwinPrimeSegments (by decide : 246415405 ≤ 246677549)
    (by decide : 246677549 ≤ 246939693) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 246939693 247463981).card = 1820 := by
  simpa using combineTwinPrimeSegments (by decide : 246939693 ≤ 247201837)
    (by decide : 247201837 ≤ 247463981) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 245366829 246415405).card = 3620 := by
  simpa using combineTwinPrimeSegments (by decide : 245366829 ≤ 245891117)
    (by decide : 245891117 ≤ 246415405) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 246415405 247463981).card = 3675 := by
  simpa using combineTwinPrimeSegments (by decide : 246415405 ≤ 246939693)
    (by decide : 246939693 ≤ 247463981) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 245366829 247463981).card = 7295 := by
  simpa using combineTwinPrimeSegments (by decide : 245366829 ≤ 246415405)
    (by decide : 246415405 ≤ 247463981) join_2_0 join_2_1

theorem total : (twinPrimeSegment 245366829 247463981).card = 7295 := join_3_0

end S117All
end Sude.GeneratedTwinScan
