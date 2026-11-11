import Sude.GeneratedTwinScan.S126C00
import Sude.GeneratedTwinScan.S126C01
import Sude.GeneratedTwinScan.S126C02
import Sude.GeneratedTwinScan.S126C03
import Sude.GeneratedTwinScan.S126C04
import Sude.GeneratedTwinScan.S126C05
import Sude.GeneratedTwinScan.S126C06
import Sude.GeneratedTwinScan.S126C07
import Sude.GeneratedTwinScan.S126C08
import Sude.GeneratedTwinScan.S126C09
import Sude.GeneratedTwinScan.S126C10
import Sude.GeneratedTwinScan.S126C11
import Sude.GeneratedTwinScan.S126C12
import Sude.GeneratedTwinScan.S126C13
import Sude.GeneratedTwinScan.S126C14
import Sude.GeneratedTwinScan.S126C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S126All

theorem join_0_0 : (twinPrimeSegment 264241197 264503341).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 264241197 ≤ 264372269)
    (by decide : 264372269 ≤ 264503341) S126C00.total S126C01.total

theorem join_0_1 : (twinPrimeSegment 264503341 264765485).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 264503341 ≤ 264634413)
    (by decide : 264634413 ≤ 264765485) S126C02.total S126C03.total

theorem join_0_2 : (twinPrimeSegment 264765485 265027629).card = 962 := by
  simpa using combineTwinPrimeSegments (by decide : 264765485 ≤ 264896557)
    (by decide : 264896557 ≤ 265027629) S126C04.total S126C05.total

theorem join_0_3 : (twinPrimeSegment 265027629 265289773).card = 927 := by
  simpa using combineTwinPrimeSegments (by decide : 265027629 ≤ 265158701)
    (by decide : 265158701 ≤ 265289773) S126C06.total S126C07.total

theorem join_0_4 : (twinPrimeSegment 265289773 265551917).card = 958 := by
  simpa using combineTwinPrimeSegments (by decide : 265289773 ≤ 265420845)
    (by decide : 265420845 ≤ 265551917) S126C08.total S126C09.total

theorem join_0_5 : (twinPrimeSegment 265551917 265814061).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 265551917 ≤ 265682989)
    (by decide : 265682989 ≤ 265814061) S126C10.total S126C11.total

theorem join_0_6 : (twinPrimeSegment 265814061 266076205).card = 953 := by
  simpa using combineTwinPrimeSegments (by decide : 265814061 ≤ 265945133)
    (by decide : 265945133 ≤ 266076205) S126C12.total S126C13.total

theorem join_0_7 : (twinPrimeSegment 266076205 266338349).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 266076205 ≤ 266207277)
    (by decide : 266207277 ≤ 266338349) S126C14.total S126C15.total

theorem join_1_0 : (twinPrimeSegment 264241197 264765485).card = 1819 := by
  simpa using combineTwinPrimeSegments (by decide : 264241197 ≤ 264503341)
    (by decide : 264503341 ≤ 264765485) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 264765485 265289773).card = 1889 := by
  simpa using combineTwinPrimeSegments (by decide : 264765485 ≤ 265027629)
    (by decide : 265027629 ≤ 265289773) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 265289773 265814061).card = 1877 := by
  simpa using combineTwinPrimeSegments (by decide : 265289773 ≤ 265551917)
    (by decide : 265551917 ≤ 265814061) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 265814061 266338349).card = 1814 := by
  simpa using combineTwinPrimeSegments (by decide : 265814061 ≤ 266076205)
    (by decide : 266076205 ≤ 266338349) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 264241197 265289773).card = 3708 := by
  simpa using combineTwinPrimeSegments (by decide : 264241197 ≤ 264765485)
    (by decide : 264765485 ≤ 265289773) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 265289773 266338349).card = 3691 := by
  simpa using combineTwinPrimeSegments (by decide : 265289773 ≤ 265814061)
    (by decide : 265814061 ≤ 266338349) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 264241197 266338349).card = 7399 := by
  simpa using combineTwinPrimeSegments (by decide : 264241197 ≤ 265289773)
    (by decide : 265289773 ≤ 266338349) join_2_0 join_2_1

theorem total : (twinPrimeSegment 264241197 266338349).card = 7399 := join_3_0

end S126All
end Sude.GeneratedTwinScan
