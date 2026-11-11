import Sude.GeneratedTwinScan.S186C00
import Sude.GeneratedTwinScan.S186C01
import Sude.GeneratedTwinScan.S186C02
import Sude.GeneratedTwinScan.S186C03
import Sude.GeneratedTwinScan.S186C04
import Sude.GeneratedTwinScan.S186C05
import Sude.GeneratedTwinScan.S186C06
import Sude.GeneratedTwinScan.S186C07
import Sude.GeneratedTwinScan.S186C08
import Sude.GeneratedTwinScan.S186C09
import Sude.GeneratedTwinScan.S186C10
import Sude.GeneratedTwinScan.S186C11
import Sude.GeneratedTwinScan.S186C12
import Sude.GeneratedTwinScan.S186C13
import Sude.GeneratedTwinScan.S186C14
import Sude.GeneratedTwinScan.S186C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S186All

theorem join_0_0 : (twinPrimeSegment 390070317 390332461).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 390070317 ≤ 390201389)
    (by decide : 390201389 ≤ 390332461) S186C00.total S186C01.total

theorem join_0_1 : (twinPrimeSegment 390332461 390594605).card = 854 := by
  simpa using combineTwinPrimeSegments (by decide : 390332461 ≤ 390463533)
    (by decide : 390463533 ≤ 390594605) S186C02.total S186C03.total

theorem join_0_2 : (twinPrimeSegment 390594605 390856749).card = 938 := by
  simpa using combineTwinPrimeSegments (by decide : 390594605 ≤ 390725677)
    (by decide : 390725677 ≤ 390856749) S186C04.total S186C05.total

theorem join_0_3 : (twinPrimeSegment 390856749 391118893).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 390856749 ≤ 390987821)
    (by decide : 390987821 ≤ 391118893) S186C06.total S186C07.total

theorem join_0_4 : (twinPrimeSegment 391118893 391381037).card = 847 := by
  simpa using combineTwinPrimeSegments (by decide : 391118893 ≤ 391249965)
    (by decide : 391249965 ≤ 391381037) S186C08.total S186C09.total

theorem join_0_5 : (twinPrimeSegment 391381037 391643181).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 391381037 ≤ 391512109)
    (by decide : 391512109 ≤ 391643181) S186C10.total S186C11.total

theorem join_0_6 : (twinPrimeSegment 391643181 391905325).card = 911 := by
  simpa using combineTwinPrimeSegments (by decide : 391643181 ≤ 391774253)
    (by decide : 391774253 ≤ 391905325) S186C12.total S186C13.total

theorem join_0_7 : (twinPrimeSegment 391905325 392167469).card = 897 := by
  simpa using combineTwinPrimeSegments (by decide : 391905325 ≤ 392036397)
    (by decide : 392036397 ≤ 392167469) S186C14.total S186C15.total

theorem join_1_0 : (twinPrimeSegment 390070317 390594605).card = 1739 := by
  simpa using combineTwinPrimeSegments (by decide : 390070317 ≤ 390332461)
    (by decide : 390332461 ≤ 390594605) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 390594605 391118893).card = 1814 := by
  simpa using combineTwinPrimeSegments (by decide : 390594605 ≤ 390856749)
    (by decide : 390856749 ≤ 391118893) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 391118893 391643181).card = 1710 := by
  simpa using combineTwinPrimeSegments (by decide : 391118893 ≤ 391381037)
    (by decide : 391381037 ≤ 391643181) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 391643181 392167469).card = 1808 := by
  simpa using combineTwinPrimeSegments (by decide : 391643181 ≤ 391905325)
    (by decide : 391905325 ≤ 392167469) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 390070317 391118893).card = 3553 := by
  simpa using combineTwinPrimeSegments (by decide : 390070317 ≤ 390594605)
    (by decide : 390594605 ≤ 391118893) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 391118893 392167469).card = 3518 := by
  simpa using combineTwinPrimeSegments (by decide : 391118893 ≤ 391643181)
    (by decide : 391643181 ≤ 392167469) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 390070317 392167469).card = 7071 := by
  simpa using combineTwinPrimeSegments (by decide : 390070317 ≤ 391118893)
    (by decide : 391118893 ≤ 392167469) join_2_0 join_2_1

theorem total : (twinPrimeSegment 390070317 392167469).card = 7071 := join_3_0

end S186All
end Sude.GeneratedTwinScan
