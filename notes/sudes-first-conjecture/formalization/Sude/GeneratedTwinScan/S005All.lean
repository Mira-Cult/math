import Sude.GeneratedTwinScan.S005C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S005All

theorem join_0_0 : (twinPrimeSegment 10485805 10747949).card = 1343 := by
  simpa using combineTwinPrimeSegments (by decide : 10485805 ≤ 10616877)
    (by decide : 10616877 ≤ 10747949) S005C00.total S005C01.total

theorem join_0_1 : (twinPrimeSegment 10747949 11010093).card = 1277 := by
  simpa using combineTwinPrimeSegments (by decide : 10747949 ≤ 10879021)
    (by decide : 10879021 ≤ 11010093) S005C02.total S005C03.total

theorem join_0_2 : (twinPrimeSegment 11010093 11272237).card = 1333 := by
  simpa using combineTwinPrimeSegments (by decide : 11010093 ≤ 11141165)
    (by decide : 11141165 ≤ 11272237) S005C04.total S005C05.total

theorem join_0_3 : (twinPrimeSegment 11272237 11534381).card = 1287 := by
  simpa using combineTwinPrimeSegments (by decide : 11272237 ≤ 11403309)
    (by decide : 11403309 ≤ 11534381) S005C06.total S005C07.total

theorem join_0_4 : (twinPrimeSegment 11534381 11796525).card = 1295 := by
  simpa using combineTwinPrimeSegments (by decide : 11534381 ≤ 11665453)
    (by decide : 11665453 ≤ 11796525) S005C08.total S005C09.total

theorem join_0_5 : (twinPrimeSegment 11796525 12058669).card = 1301 := by
  simpa using combineTwinPrimeSegments (by decide : 11796525 ≤ 11927597)
    (by decide : 11927597 ≤ 12058669) S005C10.total S005C11.total

theorem join_0_6 : (twinPrimeSegment 12058669 12320813).card = 1308 := by
  simpa using combineTwinPrimeSegments (by decide : 12058669 ≤ 12189741)
    (by decide : 12189741 ≤ 12320813) S005C12.total S005C13.total

theorem join_0_7 : (twinPrimeSegment 12320813 12582957).card = 1266 := by
  simpa using combineTwinPrimeSegments (by decide : 12320813 ≤ 12451885)
    (by decide : 12451885 ≤ 12582957) S005C14.total S005C15.total

theorem join_1_0 : (twinPrimeSegment 10485805 11010093).card = 2620 := by
  simpa using combineTwinPrimeSegments (by decide : 10485805 ≤ 10747949)
    (by decide : 10747949 ≤ 11010093) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 11010093 11534381).card = 2620 := by
  simpa using combineTwinPrimeSegments (by decide : 11010093 ≤ 11272237)
    (by decide : 11272237 ≤ 11534381) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 11534381 12058669).card = 2596 := by
  simpa using combineTwinPrimeSegments (by decide : 11534381 ≤ 11796525)
    (by decide : 11796525 ≤ 12058669) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 12058669 12582957).card = 2574 := by
  simpa using combineTwinPrimeSegments (by decide : 12058669 ≤ 12320813)
    (by decide : 12320813 ≤ 12582957) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 10485805 11534381).card = 5240 := by
  simpa using combineTwinPrimeSegments (by decide : 10485805 ≤ 11010093)
    (by decide : 11010093 ≤ 11534381) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 11534381 12582957).card = 5170 := by
  simpa using combineTwinPrimeSegments (by decide : 11534381 ≤ 12058669)
    (by decide : 12058669 ≤ 12582957) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 10485805 12582957).card = 10410 := by
  simpa using combineTwinPrimeSegments (by decide : 10485805 ≤ 11534381)
    (by decide : 11534381 ≤ 12582957) join_2_0 join_2_1

theorem total : (twinPrimeSegment 10485805 12582957).card = 10410 := join_3_0

end S005All
end Sude.GeneratedTwinScan
