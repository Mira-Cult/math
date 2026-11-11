import Sude.GeneratedTwinScan.S122C00
import Sude.GeneratedTwinScan.S122C01
import Sude.GeneratedTwinScan.S122C02
import Sude.GeneratedTwinScan.S122C03
import Sude.GeneratedTwinScan.S122C04
import Sude.GeneratedTwinScan.S122C05
import Sude.GeneratedTwinScan.S122C06
import Sude.GeneratedTwinScan.S122C07
import Sude.GeneratedTwinScan.S122C08
import Sude.GeneratedTwinScan.S122C09
import Sude.GeneratedTwinScan.S122C10
import Sude.GeneratedTwinScan.S122C11
import Sude.GeneratedTwinScan.S122C12
import Sude.GeneratedTwinScan.S122C13
import Sude.GeneratedTwinScan.S122C14
import Sude.GeneratedTwinScan.S122C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S122All

theorem join_0_0 : (twinPrimeSegment 255852589 256114733).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 255852589 ≤ 255983661)
    (by decide : 255983661 ≤ 256114733) S122C00.total S122C01.total

theorem join_0_1 : (twinPrimeSegment 256114733 256376877).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 256114733 ≤ 256245805)
    (by decide : 256245805 ≤ 256376877) S122C02.total S122C03.total

theorem join_0_2 : (twinPrimeSegment 256376877 256639021).card = 882 := by
  simpa using combineTwinPrimeSegments (by decide : 256376877 ≤ 256507949)
    (by decide : 256507949 ≤ 256639021) S122C04.total S122C05.total

theorem join_0_3 : (twinPrimeSegment 256639021 256901165).card = 935 := by
  simpa using combineTwinPrimeSegments (by decide : 256639021 ≤ 256770093)
    (by decide : 256770093 ≤ 256901165) S122C06.total S122C07.total

theorem join_0_4 : (twinPrimeSegment 256901165 257163309).card = 937 := by
  simpa using combineTwinPrimeSegments (by decide : 256901165 ≤ 257032237)
    (by decide : 257032237 ≤ 257163309) S122C08.total S122C09.total

theorem join_0_5 : (twinPrimeSegment 257163309 257425453).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 257163309 ≤ 257294381)
    (by decide : 257294381 ≤ 257425453) S122C10.total S122C11.total

theorem join_0_6 : (twinPrimeSegment 257425453 257687597).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 257425453 ≤ 257556525)
    (by decide : 257556525 ≤ 257687597) S122C12.total S122C13.total

theorem join_0_7 : (twinPrimeSegment 257687597 257949741).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 257687597 ≤ 257818669)
    (by decide : 257818669 ≤ 257949741) S122C14.total S122C15.total

theorem join_1_0 : (twinPrimeSegment 255852589 256376877).card = 1792 := by
  simpa using combineTwinPrimeSegments (by decide : 255852589 ≤ 256114733)
    (by decide : 256114733 ≤ 256376877) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 256376877 256901165).card = 1817 := by
  simpa using combineTwinPrimeSegments (by decide : 256376877 ≤ 256639021)
    (by decide : 256639021 ≤ 256901165) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 256901165 257425453).card = 1807 := by
  simpa using combineTwinPrimeSegments (by decide : 256901165 ≤ 257163309)
    (by decide : 257163309 ≤ 257425453) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 257425453 257949741).card = 1803 := by
  simpa using combineTwinPrimeSegments (by decide : 257425453 ≤ 257687597)
    (by decide : 257687597 ≤ 257949741) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 255852589 256901165).card = 3609 := by
  simpa using combineTwinPrimeSegments (by decide : 255852589 ≤ 256376877)
    (by decide : 256376877 ≤ 256901165) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 256901165 257949741).card = 3610 := by
  simpa using combineTwinPrimeSegments (by decide : 256901165 ≤ 257425453)
    (by decide : 257425453 ≤ 257949741) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 255852589 257949741).card = 7219 := by
  simpa using combineTwinPrimeSegments (by decide : 255852589 ≤ 256901165)
    (by decide : 256901165 ≤ 257949741) join_2_0 join_2_1

theorem total : (twinPrimeSegment 255852589 257949741).card = 7219 := join_3_0

end S122All
end Sude.GeneratedTwinScan
