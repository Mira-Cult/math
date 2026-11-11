import Sude.GeneratedTwinScan.S232C00
import Sude.GeneratedTwinScan.S232C01
import Sude.GeneratedTwinScan.S232C02
import Sude.GeneratedTwinScan.S232C03
import Sude.GeneratedTwinScan.S232C04
import Sude.GeneratedTwinScan.S232C05
import Sude.GeneratedTwinScan.S232C06
import Sude.GeneratedTwinScan.S232C07
import Sude.GeneratedTwinScan.S232C08
import Sude.GeneratedTwinScan.S232C09
import Sude.GeneratedTwinScan.S232C10
import Sude.GeneratedTwinScan.S232C11
import Sude.GeneratedTwinScan.S232C12
import Sude.GeneratedTwinScan.S232C13
import Sude.GeneratedTwinScan.S232C14
import Sude.GeneratedTwinScan.S232C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S232All

theorem join_0_0 : (twinPrimeSegment 486539309 486801453).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 486539309 ≤ 486670381)
    (by decide : 486670381 ≤ 486801453) S232C00.total S232C01.total

theorem join_0_1 : (twinPrimeSegment 486801453 487063597).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 486801453 ≤ 486932525)
    (by decide : 486932525 ≤ 487063597) S232C02.total S232C03.total

theorem join_0_2 : (twinPrimeSegment 487063597 487325741).card = 846 := by
  simpa using combineTwinPrimeSegments (by decide : 487063597 ≤ 487194669)
    (by decide : 487194669 ≤ 487325741) S232C04.total S232C05.total

theorem join_0_3 : (twinPrimeSegment 487325741 487587885).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 487325741 ≤ 487456813)
    (by decide : 487456813 ≤ 487587885) S232C06.total S232C07.total

theorem join_0_4 : (twinPrimeSegment 487587885 487850029).card = 849 := by
  simpa using combineTwinPrimeSegments (by decide : 487587885 ≤ 487718957)
    (by decide : 487718957 ≤ 487850029) S232C08.total S232C09.total

theorem join_0_5 : (twinPrimeSegment 487850029 488112173).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 487850029 ≤ 487981101)
    (by decide : 487981101 ≤ 488112173) S232C10.total S232C11.total

theorem join_0_6 : (twinPrimeSegment 488112173 488374317).card = 849 := by
  simpa using combineTwinPrimeSegments (by decide : 488112173 ≤ 488243245)
    (by decide : 488243245 ≤ 488374317) S232C12.total S232C13.total

theorem join_0_7 : (twinPrimeSegment 488374317 488636461).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 488374317 ≤ 488505389)
    (by decide : 488505389 ≤ 488636461) S232C14.total S232C15.total

theorem join_1_0 : (twinPrimeSegment 486539309 487063597).card = 1721 := by
  simpa using combineTwinPrimeSegments (by decide : 486539309 ≤ 486801453)
    (by decide : 486801453 ≤ 487063597) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 487063597 487587885).card = 1729 := by
  simpa using combineTwinPrimeSegments (by decide : 487063597 ≤ 487325741)
    (by decide : 487325741 ≤ 487587885) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 487587885 488112173).card = 1706 := by
  simpa using combineTwinPrimeSegments (by decide : 487587885 ≤ 487850029)
    (by decide : 487850029 ≤ 488112173) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 488112173 488636461).card = 1720 := by
  simpa using combineTwinPrimeSegments (by decide : 488112173 ≤ 488374317)
    (by decide : 488374317 ≤ 488636461) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 486539309 487587885).card = 3450 := by
  simpa using combineTwinPrimeSegments (by decide : 486539309 ≤ 487063597)
    (by decide : 487063597 ≤ 487587885) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 487587885 488636461).card = 3426 := by
  simpa using combineTwinPrimeSegments (by decide : 487587885 ≤ 488112173)
    (by decide : 488112173 ≤ 488636461) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 486539309 488636461).card = 6876 := by
  simpa using combineTwinPrimeSegments (by decide : 486539309 ≤ 487587885)
    (by decide : 487587885 ≤ 488636461) join_2_0 join_2_1

theorem total : (twinPrimeSegment 486539309 488636461).card = 6876 := join_3_0

end S232All
end Sude.GeneratedTwinScan
