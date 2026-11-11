import Sude.GeneratedTwinScan.S041C00
import Sude.GeneratedTwinScan.S041C01
import Sude.GeneratedTwinScan.S041C02
import Sude.GeneratedTwinScan.S041C03
import Sude.GeneratedTwinScan.S041C04
import Sude.GeneratedTwinScan.S041C05
import Sude.GeneratedTwinScan.S041C06
import Sude.GeneratedTwinScan.S041C07
import Sude.GeneratedTwinScan.S041C08
import Sude.GeneratedTwinScan.S041C09
import Sude.GeneratedTwinScan.S041C10
import Sude.GeneratedTwinScan.S041C11
import Sude.GeneratedTwinScan.S041C12
import Sude.GeneratedTwinScan.S041C13
import Sude.GeneratedTwinScan.S041C14
import Sude.GeneratedTwinScan.S041C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S041All

theorem join_0_0 : (twinPrimeSegment 85983277 86245421).card = 1019 := by
  simpa using combineTwinPrimeSegments (by decide : 85983277 ≤ 86114349)
    (by decide : 86114349 ≤ 86245421) S041C00.total S041C01.total

theorem join_0_1 : (twinPrimeSegment 86245421 86507565).card = 1075 := by
  simpa using combineTwinPrimeSegments (by decide : 86245421 ≤ 86376493)
    (by decide : 86376493 ≤ 86507565) S041C02.total S041C03.total

theorem join_0_2 : (twinPrimeSegment 86507565 86769709).card = 1042 := by
  simpa using combineTwinPrimeSegments (by decide : 86507565 ≤ 86638637)
    (by decide : 86638637 ≤ 86769709) S041C04.total S041C05.total

theorem join_0_3 : (twinPrimeSegment 86769709 87031853).card = 1046 := by
  simpa using combineTwinPrimeSegments (by decide : 86769709 ≤ 86900781)
    (by decide : 86900781 ≤ 87031853) S041C06.total S041C07.total

theorem join_0_4 : (twinPrimeSegment 87031853 87293997).card = 1048 := by
  simpa using combineTwinPrimeSegments (by decide : 87031853 ≤ 87162925)
    (by decide : 87162925 ≤ 87293997) S041C08.total S041C09.total

theorem join_0_5 : (twinPrimeSegment 87293997 87556141).card = 1049 := by
  simpa using combineTwinPrimeSegments (by decide : 87293997 ≤ 87425069)
    (by decide : 87425069 ≤ 87556141) S041C10.total S041C11.total

theorem join_0_6 : (twinPrimeSegment 87556141 87818285).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 87556141 ≤ 87687213)
    (by decide : 87687213 ≤ 87818285) S041C12.total S041C13.total

theorem join_0_7 : (twinPrimeSegment 87818285 88080429).card = 1074 := by
  simpa using combineTwinPrimeSegments (by decide : 87818285 ≤ 87949357)
    (by decide : 87949357 ≤ 88080429) S041C14.total S041C15.total

theorem join_1_0 : (twinPrimeSegment 85983277 86507565).card = 2094 := by
  simpa using combineTwinPrimeSegments (by decide : 85983277 ≤ 86245421)
    (by decide : 86245421 ≤ 86507565) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 86507565 87031853).card = 2088 := by
  simpa using combineTwinPrimeSegments (by decide : 86507565 ≤ 86769709)
    (by decide : 86769709 ≤ 87031853) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 87031853 87556141).card = 2097 := by
  simpa using combineTwinPrimeSegments (by decide : 87031853 ≤ 87293997)
    (by decide : 87293997 ≤ 87556141) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 87556141 88080429).card = 2056 := by
  simpa using combineTwinPrimeSegments (by decide : 87556141 ≤ 87818285)
    (by decide : 87818285 ≤ 88080429) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 85983277 87031853).card = 4182 := by
  simpa using combineTwinPrimeSegments (by decide : 85983277 ≤ 86507565)
    (by decide : 86507565 ≤ 87031853) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 87031853 88080429).card = 4153 := by
  simpa using combineTwinPrimeSegments (by decide : 87031853 ≤ 87556141)
    (by decide : 87556141 ≤ 88080429) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 85983277 88080429).card = 8335 := by
  simpa using combineTwinPrimeSegments (by decide : 85983277 ≤ 87031853)
    (by decide : 87031853 ≤ 88080429) join_2_0 join_2_1

theorem total : (twinPrimeSegment 85983277 88080429).card = 8335 := join_3_0

end S041All
end Sude.GeneratedTwinScan
