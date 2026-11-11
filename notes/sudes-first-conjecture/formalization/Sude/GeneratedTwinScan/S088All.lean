import Sude.GeneratedTwinScan.S088C00
import Sude.GeneratedTwinScan.S088C01
import Sude.GeneratedTwinScan.S088C02
import Sude.GeneratedTwinScan.S088C03
import Sude.GeneratedTwinScan.S088C04
import Sude.GeneratedTwinScan.S088C05
import Sude.GeneratedTwinScan.S088C06
import Sude.GeneratedTwinScan.S088C07
import Sude.GeneratedTwinScan.S088C08
import Sude.GeneratedTwinScan.S088C09
import Sude.GeneratedTwinScan.S088C10
import Sude.GeneratedTwinScan.S088C11
import Sude.GeneratedTwinScan.S088C12
import Sude.GeneratedTwinScan.S088C13
import Sude.GeneratedTwinScan.S088C14
import Sude.GeneratedTwinScan.S088C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S088All

theorem join_0_0 : (twinPrimeSegment 184549421 184811565).card = 980 := by
  simpa using combineTwinPrimeSegments (by decide : 184549421 ≤ 184680493)
    (by decide : 184680493 ≤ 184811565) S088C00.total S088C01.total

theorem join_0_1 : (twinPrimeSegment 184811565 185073709).card = 927 := by
  simpa using combineTwinPrimeSegments (by decide : 184811565 ≤ 184942637)
    (by decide : 184942637 ≤ 185073709) S088C02.total S088C03.total

theorem join_0_2 : (twinPrimeSegment 185073709 185335853).card = 987 := by
  simpa using combineTwinPrimeSegments (by decide : 185073709 ≤ 185204781)
    (by decide : 185204781 ≤ 185335853) S088C04.total S088C05.total

theorem join_0_3 : (twinPrimeSegment 185335853 185597997).card = 935 := by
  simpa using combineTwinPrimeSegments (by decide : 185335853 ≤ 185466925)
    (by decide : 185466925 ≤ 185597997) S088C06.total S088C07.total

theorem join_0_4 : (twinPrimeSegment 185597997 185860141).card = 931 := by
  simpa using combineTwinPrimeSegments (by decide : 185597997 ≤ 185729069)
    (by decide : 185729069 ≤ 185860141) S088C08.total S088C09.total

theorem join_0_5 : (twinPrimeSegment 185860141 186122285).card = 952 := by
  simpa using combineTwinPrimeSegments (by decide : 185860141 ≤ 185991213)
    (by decide : 185991213 ≤ 186122285) S088C10.total S088C11.total

theorem join_0_6 : (twinPrimeSegment 186122285 186384429).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 186122285 ≤ 186253357)
    (by decide : 186253357 ≤ 186384429) S088C12.total S088C13.total

theorem join_0_7 : (twinPrimeSegment 186384429 186646573).card = 973 := by
  simpa using combineTwinPrimeSegments (by decide : 186384429 ≤ 186515501)
    (by decide : 186515501 ≤ 186646573) S088C14.total S088C15.total

theorem join_1_0 : (twinPrimeSegment 184549421 185073709).card = 1907 := by
  simpa using combineTwinPrimeSegments (by decide : 184549421 ≤ 184811565)
    (by decide : 184811565 ≤ 185073709) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 185073709 185597997).card = 1922 := by
  simpa using combineTwinPrimeSegments (by decide : 185073709 ≤ 185335853)
    (by decide : 185335853 ≤ 185597997) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 185597997 186122285).card = 1883 := by
  simpa using combineTwinPrimeSegments (by decide : 185597997 ≤ 185860141)
    (by decide : 185860141 ≤ 186122285) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 186122285 186646573).card = 1937 := by
  simpa using combineTwinPrimeSegments (by decide : 186122285 ≤ 186384429)
    (by decide : 186384429 ≤ 186646573) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 184549421 185597997).card = 3829 := by
  simpa using combineTwinPrimeSegments (by decide : 184549421 ≤ 185073709)
    (by decide : 185073709 ≤ 185597997) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 185597997 186646573).card = 3820 := by
  simpa using combineTwinPrimeSegments (by decide : 185597997 ≤ 186122285)
    (by decide : 186122285 ≤ 186646573) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 184549421 186646573).card = 7649 := by
  simpa using combineTwinPrimeSegments (by decide : 184549421 ≤ 185597997)
    (by decide : 185597997 ≤ 186646573) join_2_0 join_2_1

theorem total : (twinPrimeSegment 184549421 186646573).card = 7649 := join_3_0

end S088All
end Sude.GeneratedTwinScan
