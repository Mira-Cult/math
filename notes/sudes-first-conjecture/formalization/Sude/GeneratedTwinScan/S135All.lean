import Sude.GeneratedTwinScan.S135C00
import Sude.GeneratedTwinScan.S135C01
import Sude.GeneratedTwinScan.S135C02
import Sude.GeneratedTwinScan.S135C03
import Sude.GeneratedTwinScan.S135C04
import Sude.GeneratedTwinScan.S135C05
import Sude.GeneratedTwinScan.S135C06
import Sude.GeneratedTwinScan.S135C07
import Sude.GeneratedTwinScan.S135C08
import Sude.GeneratedTwinScan.S135C09
import Sude.GeneratedTwinScan.S135C10
import Sude.GeneratedTwinScan.S135C11
import Sude.GeneratedTwinScan.S135C12
import Sude.GeneratedTwinScan.S135C13
import Sude.GeneratedTwinScan.S135C14
import Sude.GeneratedTwinScan.S135C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S135All

theorem join_0_0 : (twinPrimeSegment 283115565 283377709).card = 921 := by
  simpa using combineTwinPrimeSegments (by decide : 283115565 ≤ 283246637)
    (by decide : 283246637 ≤ 283377709) S135C00.total S135C01.total

theorem join_0_1 : (twinPrimeSegment 283377709 283639853).card = 897 := by
  simpa using combineTwinPrimeSegments (by decide : 283377709 ≤ 283508781)
    (by decide : 283508781 ≤ 283639853) S135C02.total S135C03.total

theorem join_0_2 : (twinPrimeSegment 283639853 283901997).card = 946 := by
  simpa using combineTwinPrimeSegments (by decide : 283639853 ≤ 283770925)
    (by decide : 283770925 ≤ 283901997) S135C04.total S135C05.total

theorem join_0_3 : (twinPrimeSegment 283901997 284164141).card = 887 := by
  simpa using combineTwinPrimeSegments (by decide : 283901997 ≤ 284033069)
    (by decide : 284033069 ≤ 284164141) S135C06.total S135C07.total

theorem join_0_4 : (twinPrimeSegment 284164141 284426285).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 284164141 ≤ 284295213)
    (by decide : 284295213 ≤ 284426285) S135C08.total S135C09.total

theorem join_0_5 : (twinPrimeSegment 284426285 284688429).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 284426285 ≤ 284557357)
    (by decide : 284557357 ≤ 284688429) S135C10.total S135C11.total

theorem join_0_6 : (twinPrimeSegment 284688429 284950573).card = 949 := by
  simpa using combineTwinPrimeSegments (by decide : 284688429 ≤ 284819501)
    (by decide : 284819501 ≤ 284950573) S135C12.total S135C13.total

theorem join_0_7 : (twinPrimeSegment 284950573 285212717).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 284950573 ≤ 285081645)
    (by decide : 285081645 ≤ 285212717) S135C14.total S135C15.total

theorem join_1_0 : (twinPrimeSegment 283115565 283639853).card = 1818 := by
  simpa using combineTwinPrimeSegments (by decide : 283115565 ≤ 283377709)
    (by decide : 283377709 ≤ 283639853) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 283639853 284164141).card = 1833 := by
  simpa using combineTwinPrimeSegments (by decide : 283639853 ≤ 283901997)
    (by decide : 283901997 ≤ 284164141) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 284164141 284688429).card = 1814 := by
  simpa using combineTwinPrimeSegments (by decide : 284164141 ≤ 284426285)
    (by decide : 284426285 ≤ 284688429) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 284688429 285212717).card = 1847 := by
  simpa using combineTwinPrimeSegments (by decide : 284688429 ≤ 284950573)
    (by decide : 284950573 ≤ 285212717) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 283115565 284164141).card = 3651 := by
  simpa using combineTwinPrimeSegments (by decide : 283115565 ≤ 283639853)
    (by decide : 283639853 ≤ 284164141) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 284164141 285212717).card = 3661 := by
  simpa using combineTwinPrimeSegments (by decide : 284164141 ≤ 284688429)
    (by decide : 284688429 ≤ 285212717) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 283115565 285212717).card = 7312 := by
  simpa using combineTwinPrimeSegments (by decide : 283115565 ≤ 284164141)
    (by decide : 284164141 ≤ 285212717) join_2_0 join_2_1

theorem total : (twinPrimeSegment 283115565 285212717).card = 7312 := join_3_0

end S135All
end Sude.GeneratedTwinScan
