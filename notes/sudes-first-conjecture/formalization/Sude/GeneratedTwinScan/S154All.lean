import Sude.GeneratedTwinScan.S154C00
import Sude.GeneratedTwinScan.S154C01
import Sude.GeneratedTwinScan.S154C02
import Sude.GeneratedTwinScan.S154C03
import Sude.GeneratedTwinScan.S154C04
import Sude.GeneratedTwinScan.S154C05
import Sude.GeneratedTwinScan.S154C06
import Sude.GeneratedTwinScan.S154C07
import Sude.GeneratedTwinScan.S154C08
import Sude.GeneratedTwinScan.S154C09
import Sude.GeneratedTwinScan.S154C10
import Sude.GeneratedTwinScan.S154C11
import Sude.GeneratedTwinScan.S154C12
import Sude.GeneratedTwinScan.S154C13
import Sude.GeneratedTwinScan.S154C14
import Sude.GeneratedTwinScan.S154C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S154All

theorem join_0_0 : (twinPrimeSegment 322961453 323223597).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 322961453 ≤ 323092525)
    (by decide : 323092525 ≤ 323223597) S154C00.total S154C01.total

theorem join_0_1 : (twinPrimeSegment 323223597 323485741).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 323223597 ≤ 323354669)
    (by decide : 323354669 ≤ 323485741) S154C02.total S154C03.total

theorem join_0_2 : (twinPrimeSegment 323485741 323747885).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 323485741 ≤ 323616813)
    (by decide : 323616813 ≤ 323747885) S154C04.total S154C05.total

theorem join_0_3 : (twinPrimeSegment 323747885 324010029).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 323747885 ≤ 323878957)
    (by decide : 323878957 ≤ 324010029) S154C06.total S154C07.total

theorem join_0_4 : (twinPrimeSegment 324010029 324272173).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 324010029 ≤ 324141101)
    (by decide : 324141101 ≤ 324272173) S154C08.total S154C09.total

theorem join_0_5 : (twinPrimeSegment 324272173 324534317).card = 937 := by
  simpa using combineTwinPrimeSegments (by decide : 324272173 ≤ 324403245)
    (by decide : 324403245 ≤ 324534317) S154C10.total S154C11.total

theorem join_0_6 : (twinPrimeSegment 324534317 324796461).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 324534317 ≤ 324665389)
    (by decide : 324665389 ≤ 324796461) S154C12.total S154C13.total

theorem join_0_7 : (twinPrimeSegment 324796461 325058605).card = 950 := by
  simpa using combineTwinPrimeSegments (by decide : 324796461 ≤ 324927533)
    (by decide : 324927533 ≤ 325058605) S154C14.total S154C15.total

theorem join_1_0 : (twinPrimeSegment 322961453 323485741).card = 1833 := by
  simpa using combineTwinPrimeSegments (by decide : 322961453 ≤ 323223597)
    (by decide : 323223597 ≤ 323485741) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 323485741 324010029).card = 1820 := by
  simpa using combineTwinPrimeSegments (by decide : 323485741 ≤ 323747885)
    (by decide : 323747885 ≤ 324010029) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 324010029 324534317).card = 1800 := by
  simpa using combineTwinPrimeSegments (by decide : 324010029 ≤ 324272173)
    (by decide : 324272173 ≤ 324534317) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 324534317 325058605).card = 1869 := by
  simpa using combineTwinPrimeSegments (by decide : 324534317 ≤ 324796461)
    (by decide : 324796461 ≤ 325058605) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 322961453 324010029).card = 3653 := by
  simpa using combineTwinPrimeSegments (by decide : 322961453 ≤ 323485741)
    (by decide : 323485741 ≤ 324010029) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 324010029 325058605).card = 3669 := by
  simpa using combineTwinPrimeSegments (by decide : 324010029 ≤ 324534317)
    (by decide : 324534317 ≤ 325058605) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 322961453 325058605).card = 7322 := by
  simpa using combineTwinPrimeSegments (by decide : 322961453 ≤ 324010029)
    (by decide : 324010029 ≤ 325058605) join_2_0 join_2_1

theorem total : (twinPrimeSegment 322961453 325058605).card = 7322 := join_3_0

end S154All
end Sude.GeneratedTwinScan
