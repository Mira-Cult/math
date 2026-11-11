import Sude.GeneratedTwinScan.S054C00
import Sude.GeneratedTwinScan.S054C01
import Sude.GeneratedTwinScan.S054C02
import Sude.GeneratedTwinScan.S054C03
import Sude.GeneratedTwinScan.S054C04
import Sude.GeneratedTwinScan.S054C05
import Sude.GeneratedTwinScan.S054C06
import Sude.GeneratedTwinScan.S054C07
import Sude.GeneratedTwinScan.S054C08
import Sude.GeneratedTwinScan.S054C09
import Sude.GeneratedTwinScan.S054C10
import Sude.GeneratedTwinScan.S054C11
import Sude.GeneratedTwinScan.S054C12
import Sude.GeneratedTwinScan.S054C13
import Sude.GeneratedTwinScan.S054C14
import Sude.GeneratedTwinScan.S054C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S054All

theorem join_0_0 : (twinPrimeSegment 113246253 113508397).card = 988 := by
  simpa using combineTwinPrimeSegments (by decide : 113246253 ≤ 113377325)
    (by decide : 113377325 ≤ 113508397) S054C00.total S054C01.total

theorem join_0_1 : (twinPrimeSegment 113508397 113770541).card = 1021 := by
  simpa using combineTwinPrimeSegments (by decide : 113508397 ≤ 113639469)
    (by decide : 113639469 ≤ 113770541) S054C02.total S054C03.total

theorem join_0_2 : (twinPrimeSegment 113770541 114032685).card = 965 := by
  simpa using combineTwinPrimeSegments (by decide : 113770541 ≤ 113901613)
    (by decide : 113901613 ≤ 114032685) S054C04.total S054C05.total

theorem join_0_3 : (twinPrimeSegment 114032685 114294829).card = 1018 := by
  simpa using combineTwinPrimeSegments (by decide : 114032685 ≤ 114163757)
    (by decide : 114163757 ≤ 114294829) S054C06.total S054C07.total

theorem join_0_4 : (twinPrimeSegment 114294829 114556973).card = 1016 := by
  simpa using combineTwinPrimeSegments (by decide : 114294829 ≤ 114425901)
    (by decide : 114425901 ≤ 114556973) S054C08.total S054C09.total

theorem join_0_5 : (twinPrimeSegment 114556973 114819117).card = 988 := by
  simpa using combineTwinPrimeSegments (by decide : 114556973 ≤ 114688045)
    (by decide : 114688045 ≤ 114819117) S054C10.total S054C11.total

theorem join_0_6 : (twinPrimeSegment 114819117 115081261).card = 1039 := by
  simpa using combineTwinPrimeSegments (by decide : 114819117 ≤ 114950189)
    (by decide : 114950189 ≤ 115081261) S054C12.total S054C13.total

theorem join_0_7 : (twinPrimeSegment 115081261 115343405).card = 1022 := by
  simpa using combineTwinPrimeSegments (by decide : 115081261 ≤ 115212333)
    (by decide : 115212333 ≤ 115343405) S054C14.total S054C15.total

theorem join_1_0 : (twinPrimeSegment 113246253 113770541).card = 2009 := by
  simpa using combineTwinPrimeSegments (by decide : 113246253 ≤ 113508397)
    (by decide : 113508397 ≤ 113770541) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 113770541 114294829).card = 1983 := by
  simpa using combineTwinPrimeSegments (by decide : 113770541 ≤ 114032685)
    (by decide : 114032685 ≤ 114294829) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 114294829 114819117).card = 2004 := by
  simpa using combineTwinPrimeSegments (by decide : 114294829 ≤ 114556973)
    (by decide : 114556973 ≤ 114819117) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 114819117 115343405).card = 2061 := by
  simpa using combineTwinPrimeSegments (by decide : 114819117 ≤ 115081261)
    (by decide : 115081261 ≤ 115343405) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 113246253 114294829).card = 3992 := by
  simpa using combineTwinPrimeSegments (by decide : 113246253 ≤ 113770541)
    (by decide : 113770541 ≤ 114294829) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 114294829 115343405).card = 4065 := by
  simpa using combineTwinPrimeSegments (by decide : 114294829 ≤ 114819117)
    (by decide : 114819117 ≤ 115343405) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 113246253 115343405).card = 8057 := by
  simpa using combineTwinPrimeSegments (by decide : 113246253 ≤ 114294829)
    (by decide : 114294829 ≤ 115343405) join_2_0 join_2_1

theorem total : (twinPrimeSegment 113246253 115343405).card = 8057 := join_3_0

end S054All
end Sude.GeneratedTwinScan
