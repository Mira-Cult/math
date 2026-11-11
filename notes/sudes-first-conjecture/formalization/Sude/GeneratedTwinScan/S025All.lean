import Sude.GeneratedTwinScan.S025C00
import Sude.GeneratedTwinScan.S025C01
import Sude.GeneratedTwinScan.S025C02
import Sude.GeneratedTwinScan.S025C03
import Sude.GeneratedTwinScan.S025C04
import Sude.GeneratedTwinScan.S025C05
import Sude.GeneratedTwinScan.S025C06
import Sude.GeneratedTwinScan.S025C07
import Sude.GeneratedTwinScan.S025C08
import Sude.GeneratedTwinScan.S025C09
import Sude.GeneratedTwinScan.S025C10
import Sude.GeneratedTwinScan.S025C11
import Sude.GeneratedTwinScan.S025C12
import Sude.GeneratedTwinScan.S025C13
import Sude.GeneratedTwinScan.S025C14
import Sude.GeneratedTwinScan.S025C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S025All

theorem join_0_0 : (twinPrimeSegment 52428845 52690989).card = 1090 := by
  simpa using combineTwinPrimeSegments (by decide : 52428845 ≤ 52559917)
    (by decide : 52559917 ≤ 52690989) S025C00.total S025C01.total

theorem join_0_1 : (twinPrimeSegment 52690989 52953133).card = 1131 := by
  simpa using combineTwinPrimeSegments (by decide : 52690989 ≤ 52822061)
    (by decide : 52822061 ≤ 52953133) S025C02.total S025C03.total

theorem join_0_2 : (twinPrimeSegment 52953133 53215277).card = 1121 := by
  simpa using combineTwinPrimeSegments (by decide : 52953133 ≤ 53084205)
    (by decide : 53084205 ≤ 53215277) S025C04.total S025C05.total

theorem join_0_3 : (twinPrimeSegment 53215277 53477421).card = 1102 := by
  simpa using combineTwinPrimeSegments (by decide : 53215277 ≤ 53346349)
    (by decide : 53346349 ≤ 53477421) S025C06.total S025C07.total

theorem join_0_4 : (twinPrimeSegment 53477421 53739565).card = 1083 := by
  simpa using combineTwinPrimeSegments (by decide : 53477421 ≤ 53608493)
    (by decide : 53608493 ≤ 53739565) S025C08.total S025C09.total

theorem join_0_5 : (twinPrimeSegment 53739565 54001709).card = 1099 := by
  simpa using combineTwinPrimeSegments (by decide : 53739565 ≤ 53870637)
    (by decide : 53870637 ≤ 54001709) S025C10.total S025C11.total

theorem join_0_6 : (twinPrimeSegment 54001709 54263853).card = 1120 := by
  simpa using combineTwinPrimeSegments (by decide : 54001709 ≤ 54132781)
    (by decide : 54132781 ≤ 54263853) S025C12.total S025C13.total

theorem join_0_7 : (twinPrimeSegment 54263853 54525997).card = 1042 := by
  simpa using combineTwinPrimeSegments (by decide : 54263853 ≤ 54394925)
    (by decide : 54394925 ≤ 54525997) S025C14.total S025C15.total

theorem join_1_0 : (twinPrimeSegment 52428845 52953133).card = 2221 := by
  simpa using combineTwinPrimeSegments (by decide : 52428845 ≤ 52690989)
    (by decide : 52690989 ≤ 52953133) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 52953133 53477421).card = 2223 := by
  simpa using combineTwinPrimeSegments (by decide : 52953133 ≤ 53215277)
    (by decide : 53215277 ≤ 53477421) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 53477421 54001709).card = 2182 := by
  simpa using combineTwinPrimeSegments (by decide : 53477421 ≤ 53739565)
    (by decide : 53739565 ≤ 54001709) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 54001709 54525997).card = 2162 := by
  simpa using combineTwinPrimeSegments (by decide : 54001709 ≤ 54263853)
    (by decide : 54263853 ≤ 54525997) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 52428845 53477421).card = 4444 := by
  simpa using combineTwinPrimeSegments (by decide : 52428845 ≤ 52953133)
    (by decide : 52953133 ≤ 53477421) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 53477421 54525997).card = 4344 := by
  simpa using combineTwinPrimeSegments (by decide : 53477421 ≤ 54001709)
    (by decide : 54001709 ≤ 54525997) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 52428845 54525997).card = 8788 := by
  simpa using combineTwinPrimeSegments (by decide : 52428845 ≤ 53477421)
    (by decide : 53477421 ≤ 54525997) join_2_0 join_2_1

theorem total : (twinPrimeSegment 52428845 54525997).card = 8788 := join_3_0

end S025All
end Sude.GeneratedTwinScan
