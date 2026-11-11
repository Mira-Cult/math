import Sude.GeneratedTwinScan.S031C00
import Sude.GeneratedTwinScan.S031C01
import Sude.GeneratedTwinScan.S031C02
import Sude.GeneratedTwinScan.S031C03
import Sude.GeneratedTwinScan.S031C04
import Sude.GeneratedTwinScan.S031C05
import Sude.GeneratedTwinScan.S031C06
import Sude.GeneratedTwinScan.S031C07
import Sude.GeneratedTwinScan.S031C08
import Sude.GeneratedTwinScan.S031C09
import Sude.GeneratedTwinScan.S031C10
import Sude.GeneratedTwinScan.S031C11
import Sude.GeneratedTwinScan.S031C12
import Sude.GeneratedTwinScan.S031C13
import Sude.GeneratedTwinScan.S031C14
import Sude.GeneratedTwinScan.S031C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S031All

theorem join_0_0 : (twinPrimeSegment 65011757 65273901).card = 1065 := by
  simpa using combineTwinPrimeSegments (by decide : 65011757 ≤ 65142829)
    (by decide : 65142829 ≤ 65273901) S031C00.total S031C01.total

theorem join_0_1 : (twinPrimeSegment 65273901 65536045).card = 1073 := by
  simpa using combineTwinPrimeSegments (by decide : 65273901 ≤ 65404973)
    (by decide : 65404973 ≤ 65536045) S031C02.total S031C03.total

theorem join_0_2 : (twinPrimeSegment 65536045 65798189).card = 1055 := by
  simpa using combineTwinPrimeSegments (by decide : 65536045 ≤ 65667117)
    (by decide : 65667117 ≤ 65798189) S031C04.total S031C05.total

theorem join_0_3 : (twinPrimeSegment 65798189 66060333).card = 1031 := by
  simpa using combineTwinPrimeSegments (by decide : 65798189 ≤ 65929261)
    (by decide : 65929261 ≤ 66060333) S031C06.total S031C07.total

theorem join_0_4 : (twinPrimeSegment 66060333 66322477).card = 1051 := by
  simpa using combineTwinPrimeSegments (by decide : 66060333 ≤ 66191405)
    (by decide : 66191405 ≤ 66322477) S031C08.total S031C09.total

theorem join_0_5 : (twinPrimeSegment 66322477 66584621).card = 1113 := by
  simpa using combineTwinPrimeSegments (by decide : 66322477 ≤ 66453549)
    (by decide : 66453549 ≤ 66584621) S031C10.total S031C11.total

theorem join_0_6 : (twinPrimeSegment 66584621 66846765).card = 1043 := by
  simpa using combineTwinPrimeSegments (by decide : 66584621 ≤ 66715693)
    (by decide : 66715693 ≤ 66846765) S031C12.total S031C13.total

theorem join_0_7 : (twinPrimeSegment 66846765 67108909).card = 1114 := by
  simpa using combineTwinPrimeSegments (by decide : 66846765 ≤ 66977837)
    (by decide : 66977837 ≤ 67108909) S031C14.total S031C15.total

theorem join_1_0 : (twinPrimeSegment 65011757 65536045).card = 2138 := by
  simpa using combineTwinPrimeSegments (by decide : 65011757 ≤ 65273901)
    (by decide : 65273901 ≤ 65536045) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 65536045 66060333).card = 2086 := by
  simpa using combineTwinPrimeSegments (by decide : 65536045 ≤ 65798189)
    (by decide : 65798189 ≤ 66060333) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 66060333 66584621).card = 2164 := by
  simpa using combineTwinPrimeSegments (by decide : 66060333 ≤ 66322477)
    (by decide : 66322477 ≤ 66584621) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 66584621 67108909).card = 2157 := by
  simpa using combineTwinPrimeSegments (by decide : 66584621 ≤ 66846765)
    (by decide : 66846765 ≤ 67108909) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 65011757 66060333).card = 4224 := by
  simpa using combineTwinPrimeSegments (by decide : 65011757 ≤ 65536045)
    (by decide : 65536045 ≤ 66060333) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 66060333 67108909).card = 4321 := by
  simpa using combineTwinPrimeSegments (by decide : 66060333 ≤ 66584621)
    (by decide : 66584621 ≤ 67108909) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 65011757 67108909).card = 8545 := by
  simpa using combineTwinPrimeSegments (by decide : 65011757 ≤ 66060333)
    (by decide : 66060333 ≤ 67108909) join_2_0 join_2_1

theorem total : (twinPrimeSegment 65011757 67108909).card = 8545 := join_3_0

end S031All
end Sude.GeneratedTwinScan
