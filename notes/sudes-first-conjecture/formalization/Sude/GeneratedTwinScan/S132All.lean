import Sude.GeneratedTwinScan.S132C00
import Sude.GeneratedTwinScan.S132C01
import Sude.GeneratedTwinScan.S132C02
import Sude.GeneratedTwinScan.S132C03
import Sude.GeneratedTwinScan.S132C04
import Sude.GeneratedTwinScan.S132C05
import Sude.GeneratedTwinScan.S132C06
import Sude.GeneratedTwinScan.S132C07
import Sude.GeneratedTwinScan.S132C08
import Sude.GeneratedTwinScan.S132C09
import Sude.GeneratedTwinScan.S132C10
import Sude.GeneratedTwinScan.S132C11
import Sude.GeneratedTwinScan.S132C12
import Sude.GeneratedTwinScan.S132C13
import Sude.GeneratedTwinScan.S132C14
import Sude.GeneratedTwinScan.S132C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S132All

theorem join_0_0 : (twinPrimeSegment 276824109 277086253).card = 900 := by
  simpa using combineTwinPrimeSegments (by decide : 276824109 ≤ 276955181)
    (by decide : 276955181 ≤ 277086253) S132C00.total S132C01.total

theorem join_0_1 : (twinPrimeSegment 277086253 277348397).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 277086253 ≤ 277217325)
    (by decide : 277217325 ≤ 277348397) S132C02.total S132C03.total

theorem join_0_2 : (twinPrimeSegment 277348397 277610541).card = 921 := by
  simpa using combineTwinPrimeSegments (by decide : 277348397 ≤ 277479469)
    (by decide : 277479469 ≤ 277610541) S132C04.total S132C05.total

theorem join_0_3 : (twinPrimeSegment 277610541 277872685).card = 968 := by
  simpa using combineTwinPrimeSegments (by decide : 277610541 ≤ 277741613)
    (by decide : 277741613 ≤ 277872685) S132C06.total S132C07.total

theorem join_0_4 : (twinPrimeSegment 277872685 278134829).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 277872685 ≤ 278003757)
    (by decide : 278003757 ≤ 278134829) S132C08.total S132C09.total

theorem join_0_5 : (twinPrimeSegment 278134829 278396973).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 278134829 ≤ 278265901)
    (by decide : 278265901 ≤ 278396973) S132C10.total S132C11.total

theorem join_0_6 : (twinPrimeSegment 278396973 278659117).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 278396973 ≤ 278528045)
    (by decide : 278528045 ≤ 278659117) S132C12.total S132C13.total

theorem join_0_7 : (twinPrimeSegment 278659117 278921261).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 278659117 ≤ 278790189)
    (by decide : 278790189 ≤ 278921261) S132C14.total S132C15.total

theorem join_1_0 : (twinPrimeSegment 276824109 277348397).card = 1774 := by
  simpa using combineTwinPrimeSegments (by decide : 276824109 ≤ 277086253)
    (by decide : 277086253 ≤ 277348397) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 277348397 277872685).card = 1889 := by
  simpa using combineTwinPrimeSegments (by decide : 277348397 ≤ 277610541)
    (by decide : 277610541 ≤ 277872685) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 277872685 278396973).card = 1863 := by
  simpa using combineTwinPrimeSegments (by decide : 277872685 ≤ 278134829)
    (by decide : 278134829 ≤ 278396973) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 278396973 278921261).card = 1798 := by
  simpa using combineTwinPrimeSegments (by decide : 278396973 ≤ 278659117)
    (by decide : 278659117 ≤ 278921261) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 276824109 277872685).card = 3663 := by
  simpa using combineTwinPrimeSegments (by decide : 276824109 ≤ 277348397)
    (by decide : 277348397 ≤ 277872685) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 277872685 278921261).card = 3661 := by
  simpa using combineTwinPrimeSegments (by decide : 277872685 ≤ 278396973)
    (by decide : 278396973 ≤ 278921261) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 276824109 278921261).card = 7324 := by
  simpa using combineTwinPrimeSegments (by decide : 276824109 ≤ 277872685)
    (by decide : 277872685 ≤ 278921261) join_2_0 join_2_1

theorem total : (twinPrimeSegment 276824109 278921261).card = 7324 := join_3_0

end S132All
end Sude.GeneratedTwinScan
