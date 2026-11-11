import Sude.GeneratedTwinScan.S001C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S001All

theorem join_0_0 : (twinPrimeSegment 2097197 2359341).card = 1614 := by
  simpa using combineTwinPrimeSegments (by decide : 2097197 ≤ 2228269)
    (by decide : 2228269 ≤ 2359341) S001C00.total S001C01.total

theorem join_0_1 : (twinPrimeSegment 2359341 2621485).card = 1563 := by
  simpa using combineTwinPrimeSegments (by decide : 2359341 ≤ 2490413)
    (by decide : 2490413 ≤ 2621485) S001C02.total S001C03.total

theorem join_0_2 : (twinPrimeSegment 2621485 2883629).card = 1566 := by
  simpa using combineTwinPrimeSegments (by decide : 2621485 ≤ 2752557)
    (by decide : 2752557 ≤ 2883629) S001C04.total S001C05.total

theorem join_0_3 : (twinPrimeSegment 2883629 3145773).card = 1566 := by
  simpa using combineTwinPrimeSegments (by decide : 2883629 ≤ 3014701)
    (by decide : 3014701 ≤ 3145773) S001C06.total S001C07.total

theorem join_0_4 : (twinPrimeSegment 3145773 3407917).card = 1575 := by
  simpa using combineTwinPrimeSegments (by decide : 3145773 ≤ 3276845)
    (by decide : 3276845 ≤ 3407917) S001C08.total S001C09.total

theorem join_0_5 : (twinPrimeSegment 3407917 3670061).card = 1549 := by
  simpa using combineTwinPrimeSegments (by decide : 3407917 ≤ 3538989)
    (by decide : 3538989 ≤ 3670061) S001C10.total S001C11.total

theorem join_0_6 : (twinPrimeSegment 3670061 3932205).card = 1550 := by
  simpa using combineTwinPrimeSegments (by decide : 3670061 ≤ 3801133)
    (by decide : 3801133 ≤ 3932205) S001C12.total S001C13.total

theorem join_0_7 : (twinPrimeSegment 3932205 4194349).card = 1512 := by
  simpa using combineTwinPrimeSegments (by decide : 3932205 ≤ 4063277)
    (by decide : 4063277 ≤ 4194349) S001C14.total S001C15.total

theorem join_1_0 : (twinPrimeSegment 2097197 2621485).card = 3177 := by
  simpa using combineTwinPrimeSegments (by decide : 2097197 ≤ 2359341)
    (by decide : 2359341 ≤ 2621485) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 2621485 3145773).card = 3132 := by
  simpa using combineTwinPrimeSegments (by decide : 2621485 ≤ 2883629)
    (by decide : 2883629 ≤ 3145773) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 3145773 3670061).card = 3124 := by
  simpa using combineTwinPrimeSegments (by decide : 3145773 ≤ 3407917)
    (by decide : 3407917 ≤ 3670061) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 3670061 4194349).card = 3062 := by
  simpa using combineTwinPrimeSegments (by decide : 3670061 ≤ 3932205)
    (by decide : 3932205 ≤ 4194349) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 2097197 3145773).card = 6309 := by
  simpa using combineTwinPrimeSegments (by decide : 2097197 ≤ 2621485)
    (by decide : 2621485 ≤ 3145773) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 3145773 4194349).card = 6186 := by
  simpa using combineTwinPrimeSegments (by decide : 3145773 ≤ 3670061)
    (by decide : 3670061 ≤ 4194349) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 2097197 4194349).card = 12495 := by
  simpa using combineTwinPrimeSegments (by decide : 2097197 ≤ 3145773)
    (by decide : 3145773 ≤ 4194349) join_2_0 join_2_1

theorem total : (twinPrimeSegment 2097197 4194349).card = 12495 := join_3_0

end S001All
end Sude.GeneratedTwinScan
