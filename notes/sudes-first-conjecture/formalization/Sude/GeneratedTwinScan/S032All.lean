import Sude.GeneratedTwinScan.S032C00
import Sude.GeneratedTwinScan.S032C01
import Sude.GeneratedTwinScan.S032C02
import Sude.GeneratedTwinScan.S032C03
import Sude.GeneratedTwinScan.S032C04
import Sude.GeneratedTwinScan.S032C05
import Sude.GeneratedTwinScan.S032C06
import Sude.GeneratedTwinScan.S032C07
import Sude.GeneratedTwinScan.S032C08
import Sude.GeneratedTwinScan.S032C09
import Sude.GeneratedTwinScan.S032C10
import Sude.GeneratedTwinScan.S032C11
import Sude.GeneratedTwinScan.S032C12
import Sude.GeneratedTwinScan.S032C13
import Sude.GeneratedTwinScan.S032C14
import Sude.GeneratedTwinScan.S032C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S032All

theorem join_0_0 : (twinPrimeSegment 67108909 67371053).card = 1070 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 67239981)
    (by decide : 67239981 ≤ 67371053) S032C00.total S032C01.total

theorem join_0_1 : (twinPrimeSegment 67371053 67633197).card = 1101 := by
  simpa using combineTwinPrimeSegments (by decide : 67371053 ≤ 67502125)
    (by decide : 67502125 ≤ 67633197) S032C02.total S032C03.total

theorem join_0_2 : (twinPrimeSegment 67633197 67895341).card = 1077 := by
  simpa using combineTwinPrimeSegments (by decide : 67633197 ≤ 67764269)
    (by decide : 67764269 ≤ 67895341) S032C04.total S032C05.total

theorem join_0_3 : (twinPrimeSegment 67895341 68157485).card = 1095 := by
  simpa using combineTwinPrimeSegments (by decide : 67895341 ≤ 68026413)
    (by decide : 68026413 ≤ 68157485) S032C06.total S032C07.total

theorem join_0_4 : (twinPrimeSegment 68157485 68419629).card = 1074 := by
  simpa using combineTwinPrimeSegments (by decide : 68157485 ≤ 68288557)
    (by decide : 68288557 ≤ 68419629) S032C08.total S032C09.total

theorem join_0_5 : (twinPrimeSegment 68419629 68681773).card = 1076 := by
  simpa using combineTwinPrimeSegments (by decide : 68419629 ≤ 68550701)
    (by decide : 68550701 ≤ 68681773) S032C10.total S032C11.total

theorem join_0_6 : (twinPrimeSegment 68681773 68943917).card = 1064 := by
  simpa using combineTwinPrimeSegments (by decide : 68681773 ≤ 68812845)
    (by decide : 68812845 ≤ 68943917) S032C12.total S032C13.total

theorem join_0_7 : (twinPrimeSegment 68943917 69206061).card = 1058 := by
  simpa using combineTwinPrimeSegments (by decide : 68943917 ≤ 69074989)
    (by decide : 69074989 ≤ 69206061) S032C14.total S032C15.total

theorem join_1_0 : (twinPrimeSegment 67108909 67633197).card = 2171 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 67371053)
    (by decide : 67371053 ≤ 67633197) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 67633197 68157485).card = 2172 := by
  simpa using combineTwinPrimeSegments (by decide : 67633197 ≤ 67895341)
    (by decide : 67895341 ≤ 68157485) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 68157485 68681773).card = 2150 := by
  simpa using combineTwinPrimeSegments (by decide : 68157485 ≤ 68419629)
    (by decide : 68419629 ≤ 68681773) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 68681773 69206061).card = 2122 := by
  simpa using combineTwinPrimeSegments (by decide : 68681773 ≤ 68943917)
    (by decide : 68943917 ≤ 69206061) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 67108909 68157485).card = 4343 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 67633197)
    (by decide : 67633197 ≤ 68157485) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 68157485 69206061).card = 4272 := by
  simpa using combineTwinPrimeSegments (by decide : 68157485 ≤ 68681773)
    (by decide : 68681773 ≤ 69206061) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 67108909 69206061).card = 8615 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 68157485)
    (by decide : 68157485 ≤ 69206061) join_2_0 join_2_1

theorem total : (twinPrimeSegment 67108909 69206061).card = 8615 := join_3_0

end S032All
end Sude.GeneratedTwinScan
