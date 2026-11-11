import Sude.GeneratedTwinScan.S076C00
import Sude.GeneratedTwinScan.S076C01
import Sude.GeneratedTwinScan.S076C02
import Sude.GeneratedTwinScan.S076C03
import Sude.GeneratedTwinScan.S076C04
import Sude.GeneratedTwinScan.S076C05
import Sude.GeneratedTwinScan.S076C06
import Sude.GeneratedTwinScan.S076C07
import Sude.GeneratedTwinScan.S076C08
import Sude.GeneratedTwinScan.S076C09
import Sude.GeneratedTwinScan.S076C10
import Sude.GeneratedTwinScan.S076C11
import Sude.GeneratedTwinScan.S076C12
import Sude.GeneratedTwinScan.S076C13
import Sude.GeneratedTwinScan.S076C14
import Sude.GeneratedTwinScan.S076C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S076All

theorem join_0_0 : (twinPrimeSegment 159383597 159645741).card = 930 := by
  simpa using combineTwinPrimeSegments (by decide : 159383597 ≤ 159514669)
    (by decide : 159514669 ≤ 159645741) S076C00.total S076C01.total

theorem join_0_1 : (twinPrimeSegment 159645741 159907885).card = 978 := by
  simpa using combineTwinPrimeSegments (by decide : 159645741 ≤ 159776813)
    (by decide : 159776813 ≤ 159907885) S076C02.total S076C03.total

theorem join_0_2 : (twinPrimeSegment 159907885 160170029).card = 941 := by
  simpa using combineTwinPrimeSegments (by decide : 159907885 ≤ 160038957)
    (by decide : 160038957 ≤ 160170029) S076C04.total S076C05.total

theorem join_0_3 : (twinPrimeSegment 160170029 160432173).card = 963 := by
  simpa using combineTwinPrimeSegments (by decide : 160170029 ≤ 160301101)
    (by decide : 160301101 ≤ 160432173) S076C06.total S076C07.total

theorem join_0_4 : (twinPrimeSegment 160432173 160694317).card = 948 := by
  simpa using combineTwinPrimeSegments (by decide : 160432173 ≤ 160563245)
    (by decide : 160563245 ≤ 160694317) S076C08.total S076C09.total

theorem join_0_5 : (twinPrimeSegment 160694317 160956461).card = 952 := by
  simpa using combineTwinPrimeSegments (by decide : 160694317 ≤ 160825389)
    (by decide : 160825389 ≤ 160956461) S076C10.total S076C11.total

theorem join_0_6 : (twinPrimeSegment 160956461 161218605).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 160956461 ≤ 161087533)
    (by decide : 161087533 ≤ 161218605) S076C12.total S076C13.total

theorem join_0_7 : (twinPrimeSegment 161218605 161480749).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 161218605 ≤ 161349677)
    (by decide : 161349677 ≤ 161480749) S076C14.total S076C15.total

theorem join_1_0 : (twinPrimeSegment 159383597 159907885).card = 1908 := by
  simpa using combineTwinPrimeSegments (by decide : 159383597 ≤ 159645741)
    (by decide : 159645741 ≤ 159907885) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 159907885 160432173).card = 1904 := by
  simpa using combineTwinPrimeSegments (by decide : 159907885 ≤ 160170029)
    (by decide : 160170029 ≤ 160432173) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 160432173 160956461).card = 1900 := by
  simpa using combineTwinPrimeSegments (by decide : 160432173 ≤ 160694317)
    (by decide : 160694317 ≤ 160956461) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 160956461 161480749).card = 1853 := by
  simpa using combineTwinPrimeSegments (by decide : 160956461 ≤ 161218605)
    (by decide : 161218605 ≤ 161480749) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 159383597 160432173).card = 3812 := by
  simpa using combineTwinPrimeSegments (by decide : 159383597 ≤ 159907885)
    (by decide : 159907885 ≤ 160432173) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 160432173 161480749).card = 3753 := by
  simpa using combineTwinPrimeSegments (by decide : 160432173 ≤ 160956461)
    (by decide : 160956461 ≤ 161480749) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 159383597 161480749).card = 7565 := by
  simpa using combineTwinPrimeSegments (by decide : 159383597 ≤ 160432173)
    (by decide : 160432173 ≤ 161480749) join_2_0 join_2_1

theorem total : (twinPrimeSegment 159383597 161480749).card = 7565 := join_3_0

end S076All
end Sude.GeneratedTwinScan
