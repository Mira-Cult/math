import Sude.GeneratedTwinScan.S000C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S000All

theorem join_0_0 : (twinPrimeSegment 45 262189).card = 2674 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 131117)
    (by decide : 131117 ≤ 262189) S000C00.total S000C01.total

theorem join_0_1 : (twinPrimeSegment 262189 524333).card = 2070 := by
  simpa using combineTwinPrimeSegments (by decide : 262189 ≤ 393261)
    (by decide : 393261 ≤ 524333) S000C02.total S000C03.total

theorem join_0_2 : (twinPrimeSegment 524333 786477).card = 1918 := by
  simpa using combineTwinPrimeSegments (by decide : 524333 ≤ 655405)
    (by decide : 655405 ≤ 786477) S000C04.total S000C05.total

theorem join_0_3 : (twinPrimeSegment 786477 1048621).card = 1867 := by
  simpa using combineTwinPrimeSegments (by decide : 786477 ≤ 917549)
    (by decide : 917549 ≤ 1048621) S000C06.total S000C07.total

theorem join_0_4 : (twinPrimeSegment 1048621 1310765).card = 1790 := by
  simpa using combineTwinPrimeSegments (by decide : 1048621 ≤ 1179693)
    (by decide : 1179693 ≤ 1310765) S000C08.total S000C09.total

theorem join_0_5 : (twinPrimeSegment 1310765 1572909).card = 1765 := by
  simpa using combineTwinPrimeSegments (by decide : 1310765 ≤ 1441837)
    (by decide : 1441837 ≤ 1572909) S000C10.total S000C11.total

theorem join_0_6 : (twinPrimeSegment 1572909 1835053).card = 1735 := by
  simpa using combineTwinPrimeSegments (by decide : 1572909 ≤ 1703981)
    (by decide : 1703981 ≤ 1835053) S000C12.total S000C13.total

theorem join_0_7 : (twinPrimeSegment 1835053 2097197).card = 1675 := by
  simpa using combineTwinPrimeSegments (by decide : 1835053 ≤ 1966125)
    (by decide : 1966125 ≤ 2097197) S000C14.total S000C15.total

theorem join_1_0 : (twinPrimeSegment 45 524333).card = 4744 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 262189)
    (by decide : 262189 ≤ 524333) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 524333 1048621).card = 3785 := by
  simpa using combineTwinPrimeSegments (by decide : 524333 ≤ 786477)
    (by decide : 786477 ≤ 1048621) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 1048621 1572909).card = 3555 := by
  simpa using combineTwinPrimeSegments (by decide : 1048621 ≤ 1310765)
    (by decide : 1310765 ≤ 1572909) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 1572909 2097197).card = 3410 := by
  simpa using combineTwinPrimeSegments (by decide : 1572909 ≤ 1835053)
    (by decide : 1835053 ≤ 2097197) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 45 1048621).card = 8529 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 524333)
    (by decide : 524333 ≤ 1048621) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 1048621 2097197).card = 6965 := by
  simpa using combineTwinPrimeSegments (by decide : 1048621 ≤ 1572909)
    (by decide : 1572909 ≤ 2097197) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 45 2097197).card = 15494 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 1048621)
    (by decide : 1048621 ≤ 2097197) join_2_0 join_2_1

theorem total : (twinPrimeSegment 45 2097197).card = 15494 := join_3_0

end S000All
end Sude.GeneratedTwinScan
