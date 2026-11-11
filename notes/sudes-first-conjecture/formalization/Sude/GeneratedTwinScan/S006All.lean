import Sude.GeneratedTwinScan.S006C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S006All

theorem join_0_0 : (twinPrimeSegment 12582957 12845101).card = 1297 := by
  simpa using combineTwinPrimeSegments (by decide : 12582957 ≤ 12714029)
    (by decide : 12714029 ≤ 12845101) S006C00.total S006C01.total

theorem join_0_1 : (twinPrimeSegment 12845101 13107245).card = 1239 := by
  simpa using combineTwinPrimeSegments (by decide : 12845101 ≤ 12976173)
    (by decide : 12976173 ≤ 13107245) S006C02.total S006C03.total

theorem join_0_2 : (twinPrimeSegment 13107245 13369389).card = 1282 := by
  simpa using combineTwinPrimeSegments (by decide : 13107245 ≤ 13238317)
    (by decide : 13238317 ≤ 13369389) S006C04.total S006C05.total

theorem join_0_3 : (twinPrimeSegment 13369389 13631533).card = 1292 := by
  simpa using combineTwinPrimeSegments (by decide : 13369389 ≤ 13500461)
    (by decide : 13500461 ≤ 13631533) S006C06.total S006C07.total

theorem join_0_4 : (twinPrimeSegment 13631533 13893677).card = 1288 := by
  simpa using combineTwinPrimeSegments (by decide : 13631533 ≤ 13762605)
    (by decide : 13762605 ≤ 13893677) S006C08.total S006C09.total

theorem join_0_5 : (twinPrimeSegment 13893677 14155821).card = 1292 := by
  simpa using combineTwinPrimeSegments (by decide : 13893677 ≤ 14024749)
    (by decide : 14024749 ≤ 14155821) S006C10.total S006C11.total

theorem join_0_6 : (twinPrimeSegment 14155821 14417965).card = 1311 := by
  simpa using combineTwinPrimeSegments (by decide : 14155821 ≤ 14286893)
    (by decide : 14286893 ≤ 14417965) S006C12.total S006C13.total

theorem join_0_7 : (twinPrimeSegment 14417965 14680109).card = 1230 := by
  simpa using combineTwinPrimeSegments (by decide : 14417965 ≤ 14549037)
    (by decide : 14549037 ≤ 14680109) S006C14.total S006C15.total

theorem join_1_0 : (twinPrimeSegment 12582957 13107245).card = 2536 := by
  simpa using combineTwinPrimeSegments (by decide : 12582957 ≤ 12845101)
    (by decide : 12845101 ≤ 13107245) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 13107245 13631533).card = 2574 := by
  simpa using combineTwinPrimeSegments (by decide : 13107245 ≤ 13369389)
    (by decide : 13369389 ≤ 13631533) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 13631533 14155821).card = 2580 := by
  simpa using combineTwinPrimeSegments (by decide : 13631533 ≤ 13893677)
    (by decide : 13893677 ≤ 14155821) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 14155821 14680109).card = 2541 := by
  simpa using combineTwinPrimeSegments (by decide : 14155821 ≤ 14417965)
    (by decide : 14417965 ≤ 14680109) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 12582957 13631533).card = 5110 := by
  simpa using combineTwinPrimeSegments (by decide : 12582957 ≤ 13107245)
    (by decide : 13107245 ≤ 13631533) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 13631533 14680109).card = 5121 := by
  simpa using combineTwinPrimeSegments (by decide : 13631533 ≤ 14155821)
    (by decide : 14155821 ≤ 14680109) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 12582957 14680109).card = 10231 := by
  simpa using combineTwinPrimeSegments (by decide : 12582957 ≤ 13631533)
    (by decide : 13631533 ≤ 14680109) join_2_0 join_2_1

theorem total : (twinPrimeSegment 12582957 14680109).card = 10231 := join_3_0

end S006All
end Sude.GeneratedTwinScan
