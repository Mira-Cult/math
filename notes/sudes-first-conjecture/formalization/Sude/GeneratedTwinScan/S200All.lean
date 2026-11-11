import Sude.GeneratedTwinScan.S200C00
import Sude.GeneratedTwinScan.S200C01
import Sude.GeneratedTwinScan.S200C02
import Sude.GeneratedTwinScan.S200C03
import Sude.GeneratedTwinScan.S200C04
import Sude.GeneratedTwinScan.S200C05
import Sude.GeneratedTwinScan.S200C06
import Sude.GeneratedTwinScan.S200C07
import Sude.GeneratedTwinScan.S200C08
import Sude.GeneratedTwinScan.S200C09
import Sude.GeneratedTwinScan.S200C10
import Sude.GeneratedTwinScan.S200C11
import Sude.GeneratedTwinScan.S200C12
import Sude.GeneratedTwinScan.S200C13
import Sude.GeneratedTwinScan.S200C14
import Sude.GeneratedTwinScan.S200C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S200All

theorem join_0_0 : (twinPrimeSegment 419430445 419692589).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 419430445 ≤ 419561517)
    (by decide : 419561517 ≤ 419692589) S200C00.total S200C01.total

theorem join_0_1 : (twinPrimeSegment 419692589 419954733).card = 950 := by
  simpa using combineTwinPrimeSegments (by decide : 419692589 ≤ 419823661)
    (by decide : 419823661 ≤ 419954733) S200C02.total S200C03.total

theorem join_0_2 : (twinPrimeSegment 419954733 420216877).card = 873 := by
  simpa using combineTwinPrimeSegments (by decide : 419954733 ≤ 420085805)
    (by decide : 420085805 ≤ 420216877) S200C04.total S200C05.total

theorem join_0_3 : (twinPrimeSegment 420216877 420479021).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 420216877 ≤ 420347949)
    (by decide : 420347949 ≤ 420479021) S200C06.total S200C07.total

theorem join_0_4 : (twinPrimeSegment 420479021 420741165).card = 940 := by
  simpa using combineTwinPrimeSegments (by decide : 420479021 ≤ 420610093)
    (by decide : 420610093 ≤ 420741165) S200C08.total S200C09.total

theorem join_0_5 : (twinPrimeSegment 420741165 421003309).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 420741165 ≤ 420872237)
    (by decide : 420872237 ≤ 421003309) S200C10.total S200C11.total

theorem join_0_6 : (twinPrimeSegment 421003309 421265453).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 421003309 ≤ 421134381)
    (by decide : 421134381 ≤ 421265453) S200C12.total S200C13.total

theorem join_0_7 : (twinPrimeSegment 421265453 421527597).card = 850 := by
  simpa using combineTwinPrimeSegments (by decide : 421265453 ≤ 421396525)
    (by decide : 421396525 ≤ 421527597) S200C14.total S200C15.total

theorem join_1_0 : (twinPrimeSegment 419430445 419954733).card = 1827 := by
  simpa using combineTwinPrimeSegments (by decide : 419430445 ≤ 419692589)
    (by decide : 419692589 ≤ 419954733) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 419954733 420479021).card = 1753 := by
  simpa using combineTwinPrimeSegments (by decide : 419954733 ≤ 420216877)
    (by decide : 420216877 ≤ 420479021) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 420479021 421003309).card = 1839 := by
  simpa using combineTwinPrimeSegments (by decide : 420479021 ≤ 420741165)
    (by decide : 420741165 ≤ 421003309) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 421003309 421527597).card = 1712 := by
  simpa using combineTwinPrimeSegments (by decide : 421003309 ≤ 421265453)
    (by decide : 421265453 ≤ 421527597) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 419430445 420479021).card = 3580 := by
  simpa using combineTwinPrimeSegments (by decide : 419430445 ≤ 419954733)
    (by decide : 419954733 ≤ 420479021) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 420479021 421527597).card = 3551 := by
  simpa using combineTwinPrimeSegments (by decide : 420479021 ≤ 421003309)
    (by decide : 421003309 ≤ 421527597) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 419430445 421527597).card = 7131 := by
  simpa using combineTwinPrimeSegments (by decide : 419430445 ≤ 420479021)
    (by decide : 420479021 ≤ 421527597) join_2_0 join_2_1

theorem total : (twinPrimeSegment 419430445 421527597).card = 7131 := join_3_0

end S200All
end Sude.GeneratedTwinScan
