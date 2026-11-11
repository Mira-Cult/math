import Sude.GeneratedTwinScan.S092C00
import Sude.GeneratedTwinScan.S092C01
import Sude.GeneratedTwinScan.S092C02
import Sude.GeneratedTwinScan.S092C03
import Sude.GeneratedTwinScan.S092C04
import Sude.GeneratedTwinScan.S092C05
import Sude.GeneratedTwinScan.S092C06
import Sude.GeneratedTwinScan.S092C07
import Sude.GeneratedTwinScan.S092C08
import Sude.GeneratedTwinScan.S092C09
import Sude.GeneratedTwinScan.S092C10
import Sude.GeneratedTwinScan.S092C11
import Sude.GeneratedTwinScan.S092C12
import Sude.GeneratedTwinScan.S092C13
import Sude.GeneratedTwinScan.S092C14
import Sude.GeneratedTwinScan.S092C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S092All

theorem join_0_0 : (twinPrimeSegment 192938029 193200173).card = 944 := by
  simpa using combineTwinPrimeSegments (by decide : 192938029 ≤ 193069101)
    (by decide : 193069101 ≤ 193200173) S092C00.total S092C01.total

theorem join_0_1 : (twinPrimeSegment 193200173 193462317).card = 941 := by
  simpa using combineTwinPrimeSegments (by decide : 193200173 ≤ 193331245)
    (by decide : 193331245 ≤ 193462317) S092C02.total S092C03.total

theorem join_0_2 : (twinPrimeSegment 193462317 193724461).card = 984 := by
  simpa using combineTwinPrimeSegments (by decide : 193462317 ≤ 193593389)
    (by decide : 193593389 ≤ 193724461) S092C04.total S092C05.total

theorem join_0_3 : (twinPrimeSegment 193724461 193986605).card = 962 := by
  simpa using combineTwinPrimeSegments (by decide : 193724461 ≤ 193855533)
    (by decide : 193855533 ≤ 193986605) S092C06.total S092C07.total

theorem join_0_4 : (twinPrimeSegment 193986605 194248749).card = 961 := by
  simpa using combineTwinPrimeSegments (by decide : 193986605 ≤ 194117677)
    (by decide : 194117677 ≤ 194248749) S092C08.total S092C09.total

theorem join_0_5 : (twinPrimeSegment 194248749 194510893).card = 971 := by
  simpa using combineTwinPrimeSegments (by decide : 194248749 ≤ 194379821)
    (by decide : 194379821 ≤ 194510893) S092C10.total S092C11.total

theorem join_0_6 : (twinPrimeSegment 194510893 194773037).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 194510893 ≤ 194641965)
    (by decide : 194641965 ≤ 194773037) S092C12.total S092C13.total

theorem join_0_7 : (twinPrimeSegment 194773037 195035181).card = 988 := by
  simpa using combineTwinPrimeSegments (by decide : 194773037 ≤ 194904109)
    (by decide : 194904109 ≤ 195035181) S092C14.total S092C15.total

theorem join_1_0 : (twinPrimeSegment 192938029 193462317).card = 1885 := by
  simpa using combineTwinPrimeSegments (by decide : 192938029 ≤ 193200173)
    (by decide : 193200173 ≤ 193462317) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 193462317 193986605).card = 1946 := by
  simpa using combineTwinPrimeSegments (by decide : 193462317 ≤ 193724461)
    (by decide : 193724461 ≤ 193986605) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 193986605 194510893).card = 1932 := by
  simpa using combineTwinPrimeSegments (by decide : 193986605 ≤ 194248749)
    (by decide : 194248749 ≤ 194510893) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 194510893 195035181).card = 1900 := by
  simpa using combineTwinPrimeSegments (by decide : 194510893 ≤ 194773037)
    (by decide : 194773037 ≤ 195035181) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 192938029 193986605).card = 3831 := by
  simpa using combineTwinPrimeSegments (by decide : 192938029 ≤ 193462317)
    (by decide : 193462317 ≤ 193986605) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 193986605 195035181).card = 3832 := by
  simpa using combineTwinPrimeSegments (by decide : 193986605 ≤ 194510893)
    (by decide : 194510893 ≤ 195035181) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 192938029 195035181).card = 7663 := by
  simpa using combineTwinPrimeSegments (by decide : 192938029 ≤ 193986605)
    (by decide : 193986605 ≤ 195035181) join_2_0 join_2_1

theorem total : (twinPrimeSegment 192938029 195035181).card = 7663 := join_3_0

end S092All
end Sude.GeneratedTwinScan
