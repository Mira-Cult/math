import Sude.GeneratedTwinScan.S075C00
import Sude.GeneratedTwinScan.S075C01
import Sude.GeneratedTwinScan.S075C02
import Sude.GeneratedTwinScan.S075C03
import Sude.GeneratedTwinScan.S075C04
import Sude.GeneratedTwinScan.S075C05
import Sude.GeneratedTwinScan.S075C06
import Sude.GeneratedTwinScan.S075C07
import Sude.GeneratedTwinScan.S075C08
import Sude.GeneratedTwinScan.S075C09
import Sude.GeneratedTwinScan.S075C10
import Sude.GeneratedTwinScan.S075C11
import Sude.GeneratedTwinScan.S075C12
import Sude.GeneratedTwinScan.S075C13
import Sude.GeneratedTwinScan.S075C14
import Sude.GeneratedTwinScan.S075C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S075All

theorem join_0_0 : (twinPrimeSegment 157286445 157548589).card = 976 := by
  simpa using combineTwinPrimeSegments (by decide : 157286445 ≤ 157417517)
    (by decide : 157417517 ≤ 157548589) S075C00.total S075C01.total

theorem join_0_1 : (twinPrimeSegment 157548589 157810733).card = 956 := by
  simpa using combineTwinPrimeSegments (by decide : 157548589 ≤ 157679661)
    (by decide : 157679661 ≤ 157810733) S075C02.total S075C03.total

theorem join_0_2 : (twinPrimeSegment 157810733 158072877).card = 993 := by
  simpa using combineTwinPrimeSegments (by decide : 157810733 ≤ 157941805)
    (by decide : 157941805 ≤ 158072877) S075C04.total S075C05.total

theorem join_0_3 : (twinPrimeSegment 158072877 158335021).card = 985 := by
  simpa using combineTwinPrimeSegments (by decide : 158072877 ≤ 158203949)
    (by decide : 158203949 ≤ 158335021) S075C06.total S075C07.total

theorem join_0_4 : (twinPrimeSegment 158335021 158597165).card = 1007 := by
  simpa using combineTwinPrimeSegments (by decide : 158335021 ≤ 158466093)
    (by decide : 158466093 ≤ 158597165) S075C08.total S075C09.total

theorem join_0_5 : (twinPrimeSegment 158597165 158859309).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 158597165 ≤ 158728237)
    (by decide : 158728237 ≤ 158859309) S075C10.total S075C11.total

theorem join_0_6 : (twinPrimeSegment 158859309 159121453).card = 1011 := by
  simpa using combineTwinPrimeSegments (by decide : 158859309 ≤ 158990381)
    (by decide : 158990381 ≤ 159121453) S075C12.total S075C13.total

theorem join_0_7 : (twinPrimeSegment 159121453 159383597).card = 983 := by
  simpa using combineTwinPrimeSegments (by decide : 159121453 ≤ 159252525)
    (by decide : 159252525 ≤ 159383597) S075C14.total S075C15.total

theorem join_1_0 : (twinPrimeSegment 157286445 157810733).card = 1932 := by
  simpa using combineTwinPrimeSegments (by decide : 157286445 ≤ 157548589)
    (by decide : 157548589 ≤ 157810733) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 157810733 158335021).card = 1978 := by
  simpa using combineTwinPrimeSegments (by decide : 157810733 ≤ 158072877)
    (by decide : 158072877 ≤ 158335021) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 158335021 158859309).card = 1946 := by
  simpa using combineTwinPrimeSegments (by decide : 158335021 ≤ 158597165)
    (by decide : 158597165 ≤ 158859309) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 158859309 159383597).card = 1994 := by
  simpa using combineTwinPrimeSegments (by decide : 158859309 ≤ 159121453)
    (by decide : 159121453 ≤ 159383597) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 157286445 158335021).card = 3910 := by
  simpa using combineTwinPrimeSegments (by decide : 157286445 ≤ 157810733)
    (by decide : 157810733 ≤ 158335021) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 158335021 159383597).card = 3940 := by
  simpa using combineTwinPrimeSegments (by decide : 158335021 ≤ 158859309)
    (by decide : 158859309 ≤ 159383597) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 157286445 159383597).card = 7850 := by
  simpa using combineTwinPrimeSegments (by decide : 157286445 ≤ 158335021)
    (by decide : 158335021 ≤ 159383597) join_2_0 join_2_1

theorem total : (twinPrimeSegment 157286445 159383597).card = 7850 := join_3_0

end S075All
end Sude.GeneratedTwinScan
