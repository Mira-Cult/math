import Sude.GeneratedTwinScan.S213C00
import Sude.GeneratedTwinScan.S213C01
import Sude.GeneratedTwinScan.S213C02
import Sude.GeneratedTwinScan.S213C03
import Sude.GeneratedTwinScan.S213C04
import Sude.GeneratedTwinScan.S213C05
import Sude.GeneratedTwinScan.S213C06
import Sude.GeneratedTwinScan.S213C07
import Sude.GeneratedTwinScan.S213C08
import Sude.GeneratedTwinScan.S213C09
import Sude.GeneratedTwinScan.S213C10
import Sude.GeneratedTwinScan.S213C11
import Sude.GeneratedTwinScan.S213C12
import Sude.GeneratedTwinScan.S213C13
import Sude.GeneratedTwinScan.S213C14
import Sude.GeneratedTwinScan.S213C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S213All

theorem join_0_0 : (twinPrimeSegment 446693421 446955565).card = 884 := by
  simpa using combineTwinPrimeSegments (by decide : 446693421 ≤ 446824493)
    (by decide : 446824493 ≤ 446955565) S213C00.total S213C01.total

theorem join_0_1 : (twinPrimeSegment 446955565 447217709).card = 868 := by
  simpa using combineTwinPrimeSegments (by decide : 446955565 ≤ 447086637)
    (by decide : 447086637 ≤ 447217709) S213C02.total S213C03.total

theorem join_0_2 : (twinPrimeSegment 447217709 447479853).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 447217709 ≤ 447348781)
    (by decide : 447348781 ≤ 447479853) S213C04.total S213C05.total

theorem join_0_3 : (twinPrimeSegment 447479853 447741997).card = 858 := by
  simpa using combineTwinPrimeSegments (by decide : 447479853 ≤ 447610925)
    (by decide : 447610925 ≤ 447741997) S213C06.total S213C07.total

theorem join_0_4 : (twinPrimeSegment 447741997 448004141).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 447741997 ≤ 447873069)
    (by decide : 447873069 ≤ 448004141) S213C08.total S213C09.total

theorem join_0_5 : (twinPrimeSegment 448004141 448266285).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 448004141 ≤ 448135213)
    (by decide : 448135213 ≤ 448266285) S213C10.total S213C11.total

theorem join_0_6 : (twinPrimeSegment 448266285 448528429).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 448266285 ≤ 448397357)
    (by decide : 448397357 ≤ 448528429) S213C12.total S213C13.total

theorem join_0_7 : (twinPrimeSegment 448528429 448790573).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 448528429 ≤ 448659501)
    (by decide : 448659501 ≤ 448790573) S213C14.total S213C15.total

theorem join_1_0 : (twinPrimeSegment 446693421 447217709).card = 1752 := by
  simpa using combineTwinPrimeSegments (by decide : 446693421 ≤ 446955565)
    (by decide : 446955565 ≤ 447217709) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 447217709 447741997).card = 1722 := by
  simpa using combineTwinPrimeSegments (by decide : 447217709 ≤ 447479853)
    (by decide : 447479853 ≤ 447741997) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 447741997 448266285).card = 1731 := by
  simpa using combineTwinPrimeSegments (by decide : 447741997 ≤ 448004141)
    (by decide : 448004141 ≤ 448266285) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 448266285 448790573).card = 1757 := by
  simpa using combineTwinPrimeSegments (by decide : 448266285 ≤ 448528429)
    (by decide : 448528429 ≤ 448790573) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 446693421 447741997).card = 3474 := by
  simpa using combineTwinPrimeSegments (by decide : 446693421 ≤ 447217709)
    (by decide : 447217709 ≤ 447741997) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 447741997 448790573).card = 3488 := by
  simpa using combineTwinPrimeSegments (by decide : 447741997 ≤ 448266285)
    (by decide : 448266285 ≤ 448790573) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 446693421 448790573).card = 6962 := by
  simpa using combineTwinPrimeSegments (by decide : 446693421 ≤ 447741997)
    (by decide : 447741997 ≤ 448790573) join_2_0 join_2_1

theorem total : (twinPrimeSegment 446693421 448790573).card = 6962 := join_3_0

end S213All
end Sude.GeneratedTwinScan
