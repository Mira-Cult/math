import Sude.GeneratedTwinScan.S166C00
import Sude.GeneratedTwinScan.S166C01
import Sude.GeneratedTwinScan.S166C02
import Sude.GeneratedTwinScan.S166C03
import Sude.GeneratedTwinScan.S166C04
import Sude.GeneratedTwinScan.S166C05
import Sude.GeneratedTwinScan.S166C06
import Sude.GeneratedTwinScan.S166C07
import Sude.GeneratedTwinScan.S166C08
import Sude.GeneratedTwinScan.S166C09
import Sude.GeneratedTwinScan.S166C10
import Sude.GeneratedTwinScan.S166C11
import Sude.GeneratedTwinScan.S166C12
import Sude.GeneratedTwinScan.S166C13
import Sude.GeneratedTwinScan.S166C14
import Sude.GeneratedTwinScan.S166C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S166All

theorem join_0_0 : (twinPrimeSegment 348127277 348389421).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 348127277 ≤ 348258349)
    (by decide : 348258349 ≤ 348389421) S166C00.total S166C01.total

theorem join_0_1 : (twinPrimeSegment 348389421 348651565).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 348389421 ≤ 348520493)
    (by decide : 348520493 ≤ 348651565) S166C02.total S166C03.total

theorem join_0_2 : (twinPrimeSegment 348651565 348913709).card = 838 := by
  simpa using combineTwinPrimeSegments (by decide : 348651565 ≤ 348782637)
    (by decide : 348782637 ≤ 348913709) S166C04.total S166C05.total

theorem join_0_3 : (twinPrimeSegment 348913709 349175853).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 348913709 ≤ 349044781)
    (by decide : 349044781 ≤ 349175853) S166C06.total S166C07.total

theorem join_0_4 : (twinPrimeSegment 349175853 349437997).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 349175853 ≤ 349306925)
    (by decide : 349306925 ≤ 349437997) S166C08.total S166C09.total

theorem join_0_5 : (twinPrimeSegment 349437997 349700141).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 349437997 ≤ 349569069)
    (by decide : 349569069 ≤ 349700141) S166C10.total S166C11.total

theorem join_0_6 : (twinPrimeSegment 349700141 349962285).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 349700141 ≤ 349831213)
    (by decide : 349831213 ≤ 349962285) S166C12.total S166C13.total

theorem join_0_7 : (twinPrimeSegment 349962285 350224429).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 349962285 ≤ 350093357)
    (by decide : 350093357 ≤ 350224429) S166C14.total S166C15.total

theorem join_1_0 : (twinPrimeSegment 348127277 348651565).card = 1765 := by
  simpa using combineTwinPrimeSegments (by decide : 348127277 ≤ 348389421)
    (by decide : 348389421 ≤ 348651565) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 348651565 349175853).card = 1742 := by
  simpa using combineTwinPrimeSegments (by decide : 348651565 ≤ 348913709)
    (by decide : 348913709 ≤ 349175853) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 349175853 349700141).card = 1833 := by
  simpa using combineTwinPrimeSegments (by decide : 349175853 ≤ 349437997)
    (by decide : 349437997 ≤ 349700141) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 349700141 350224429).card = 1782 := by
  simpa using combineTwinPrimeSegments (by decide : 349700141 ≤ 349962285)
    (by decide : 349962285 ≤ 350224429) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 348127277 349175853).card = 3507 := by
  simpa using combineTwinPrimeSegments (by decide : 348127277 ≤ 348651565)
    (by decide : 348651565 ≤ 349175853) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 349175853 350224429).card = 3615 := by
  simpa using combineTwinPrimeSegments (by decide : 349175853 ≤ 349700141)
    (by decide : 349700141 ≤ 350224429) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 348127277 350224429).card = 7122 := by
  simpa using combineTwinPrimeSegments (by decide : 348127277 ≤ 349175853)
    (by decide : 349175853 ≤ 350224429) join_2_0 join_2_1

theorem total : (twinPrimeSegment 348127277 350224429).card = 7122 := join_3_0

end S166All
end Sude.GeneratedTwinScan
