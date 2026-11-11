import Sude.GeneratedTwinScan.S110C00
import Sude.GeneratedTwinScan.S110C01
import Sude.GeneratedTwinScan.S110C02
import Sude.GeneratedTwinScan.S110C03
import Sude.GeneratedTwinScan.S110C04
import Sude.GeneratedTwinScan.S110C05
import Sude.GeneratedTwinScan.S110C06
import Sude.GeneratedTwinScan.S110C07
import Sude.GeneratedTwinScan.S110C08
import Sude.GeneratedTwinScan.S110C09
import Sude.GeneratedTwinScan.S110C10
import Sude.GeneratedTwinScan.S110C11
import Sude.GeneratedTwinScan.S110C12
import Sude.GeneratedTwinScan.S110C13
import Sude.GeneratedTwinScan.S110C14
import Sude.GeneratedTwinScan.S110C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S110All

theorem join_0_0 : (twinPrimeSegment 230686765 230948909).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 230686765 ≤ 230817837)
    (by decide : 230817837 ≤ 230948909) S110C00.total S110C01.total

theorem join_0_1 : (twinPrimeSegment 230948909 231211053).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 230948909 ≤ 231079981)
    (by decide : 231079981 ≤ 231211053) S110C02.total S110C03.total

theorem join_0_2 : (twinPrimeSegment 231211053 231473197).card = 978 := by
  simpa using combineTwinPrimeSegments (by decide : 231211053 ≤ 231342125)
    (by decide : 231342125 ≤ 231473197) S110C04.total S110C05.total

theorem join_0_3 : (twinPrimeSegment 231473197 231735341).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 231473197 ≤ 231604269)
    (by decide : 231604269 ≤ 231735341) S110C06.total S110C07.total

theorem join_0_4 : (twinPrimeSegment 231735341 231997485).card = 909 := by
  simpa using combineTwinPrimeSegments (by decide : 231735341 ≤ 231866413)
    (by decide : 231866413 ≤ 231997485) S110C08.total S110C09.total

theorem join_0_5 : (twinPrimeSegment 231997485 232259629).card = 907 := by
  simpa using combineTwinPrimeSegments (by decide : 231997485 ≤ 232128557)
    (by decide : 232128557 ≤ 232259629) S110C10.total S110C11.total

theorem join_0_6 : (twinPrimeSegment 232259629 232521773).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 232259629 ≤ 232390701)
    (by decide : 232390701 ≤ 232521773) S110C12.total S110C13.total

theorem join_0_7 : (twinPrimeSegment 232521773 232783917).card = 949 := by
  simpa using combineTwinPrimeSegments (by decide : 232521773 ≤ 232652845)
    (by decide : 232652845 ≤ 232783917) S110C14.total S110C15.total

theorem join_1_0 : (twinPrimeSegment 230686765 231211053).card = 1776 := by
  simpa using combineTwinPrimeSegments (by decide : 230686765 ≤ 230948909)
    (by decide : 230948909 ≤ 231211053) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 231211053 231735341).card = 1877 := by
  simpa using combineTwinPrimeSegments (by decide : 231211053 ≤ 231473197)
    (by decide : 231473197 ≤ 231735341) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 231735341 232259629).card = 1816 := by
  simpa using combineTwinPrimeSegments (by decide : 231735341 ≤ 231997485)
    (by decide : 231997485 ≤ 232259629) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 232259629 232783917).card = 1873 := by
  simpa using combineTwinPrimeSegments (by decide : 232259629 ≤ 232521773)
    (by decide : 232521773 ≤ 232783917) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 230686765 231735341).card = 3653 := by
  simpa using combineTwinPrimeSegments (by decide : 230686765 ≤ 231211053)
    (by decide : 231211053 ≤ 231735341) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 231735341 232783917).card = 3689 := by
  simpa using combineTwinPrimeSegments (by decide : 231735341 ≤ 232259629)
    (by decide : 232259629 ≤ 232783917) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 230686765 232783917).card = 7342 := by
  simpa using combineTwinPrimeSegments (by decide : 230686765 ≤ 231735341)
    (by decide : 231735341 ≤ 232783917) join_2_0 join_2_1

theorem total : (twinPrimeSegment 230686765 232783917).card = 7342 := join_3_0

end S110All
end Sude.GeneratedTwinScan
