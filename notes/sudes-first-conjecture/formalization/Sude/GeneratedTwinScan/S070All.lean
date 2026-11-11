import Sude.GeneratedTwinScan.S070C00
import Sude.GeneratedTwinScan.S070C01
import Sude.GeneratedTwinScan.S070C02
import Sude.GeneratedTwinScan.S070C03
import Sude.GeneratedTwinScan.S070C04
import Sude.GeneratedTwinScan.S070C05
import Sude.GeneratedTwinScan.S070C06
import Sude.GeneratedTwinScan.S070C07
import Sude.GeneratedTwinScan.S070C08
import Sude.GeneratedTwinScan.S070C09
import Sude.GeneratedTwinScan.S070C10
import Sude.GeneratedTwinScan.S070C11
import Sude.GeneratedTwinScan.S070C12
import Sude.GeneratedTwinScan.S070C13
import Sude.GeneratedTwinScan.S070C14
import Sude.GeneratedTwinScan.S070C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S070All

theorem join_0_0 : (twinPrimeSegment 146800685 147062829).card = 1014 := by
  simpa using combineTwinPrimeSegments (by decide : 146800685 ≤ 146931757)
    (by decide : 146931757 ≤ 147062829) S070C00.total S070C01.total

theorem join_0_1 : (twinPrimeSegment 147062829 147324973).card = 963 := by
  simpa using combineTwinPrimeSegments (by decide : 147062829 ≤ 147193901)
    (by decide : 147193901 ≤ 147324973) S070C02.total S070C03.total

theorem join_0_2 : (twinPrimeSegment 147324973 147587117).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 147324973 ≤ 147456045)
    (by decide : 147456045 ≤ 147587117) S070C04.total S070C05.total

theorem join_0_3 : (twinPrimeSegment 147587117 147849261).card = 971 := by
  simpa using combineTwinPrimeSegments (by decide : 147587117 ≤ 147718189)
    (by decide : 147718189 ≤ 147849261) S070C06.total S070C07.total

theorem join_0_4 : (twinPrimeSegment 147849261 148111405).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 147849261 ≤ 147980333)
    (by decide : 147980333 ≤ 148111405) S070C08.total S070C09.total

theorem join_0_5 : (twinPrimeSegment 148111405 148373549).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 148111405 ≤ 148242477)
    (by decide : 148242477 ≤ 148373549) S070C10.total S070C11.total

theorem join_0_6 : (twinPrimeSegment 148373549 148635693).card = 971 := by
  simpa using combineTwinPrimeSegments (by decide : 148373549 ≤ 148504621)
    (by decide : 148504621 ≤ 148635693) S070C12.total S070C13.total

theorem join_0_7 : (twinPrimeSegment 148635693 148897837).card = 963 := by
  simpa using combineTwinPrimeSegments (by decide : 148635693 ≤ 148766765)
    (by decide : 148766765 ≤ 148897837) S070C14.total S070C15.total

theorem join_1_0 : (twinPrimeSegment 146800685 147324973).card = 1977 := by
  simpa using combineTwinPrimeSegments (by decide : 146800685 ≤ 147062829)
    (by decide : 147062829 ≤ 147324973) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 147324973 147849261).card = 1953 := by
  simpa using combineTwinPrimeSegments (by decide : 147324973 ≤ 147587117)
    (by decide : 147587117 ≤ 147849261) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 147849261 148373549).card = 1928 := by
  simpa using combineTwinPrimeSegments (by decide : 147849261 ≤ 148111405)
    (by decide : 148111405 ≤ 148373549) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 148373549 148897837).card = 1934 := by
  simpa using combineTwinPrimeSegments (by decide : 148373549 ≤ 148635693)
    (by decide : 148635693 ≤ 148897837) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 146800685 147849261).card = 3930 := by
  simpa using combineTwinPrimeSegments (by decide : 146800685 ≤ 147324973)
    (by decide : 147324973 ≤ 147849261) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 147849261 148897837).card = 3862 := by
  simpa using combineTwinPrimeSegments (by decide : 147849261 ≤ 148373549)
    (by decide : 148373549 ≤ 148897837) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 146800685 148897837).card = 7792 := by
  simpa using combineTwinPrimeSegments (by decide : 146800685 ≤ 147849261)
    (by decide : 147849261 ≤ 148897837) join_2_0 join_2_1

theorem total : (twinPrimeSegment 146800685 148897837).card = 7792 := join_3_0

end S070All
end Sude.GeneratedTwinScan
