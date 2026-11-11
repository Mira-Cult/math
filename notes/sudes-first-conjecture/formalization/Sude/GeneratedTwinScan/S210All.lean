import Sude.GeneratedTwinScan.S210C00
import Sude.GeneratedTwinScan.S210C01
import Sude.GeneratedTwinScan.S210C02
import Sude.GeneratedTwinScan.S210C03
import Sude.GeneratedTwinScan.S210C04
import Sude.GeneratedTwinScan.S210C05
import Sude.GeneratedTwinScan.S210C06
import Sude.GeneratedTwinScan.S210C07
import Sude.GeneratedTwinScan.S210C08
import Sude.GeneratedTwinScan.S210C09
import Sude.GeneratedTwinScan.S210C10
import Sude.GeneratedTwinScan.S210C11
import Sude.GeneratedTwinScan.S210C12
import Sude.GeneratedTwinScan.S210C13
import Sude.GeneratedTwinScan.S210C14
import Sude.GeneratedTwinScan.S210C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S210All

theorem join_0_0 : (twinPrimeSegment 440401965 440664109).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 440401965 ≤ 440533037)
    (by decide : 440533037 ≤ 440664109) S210C00.total S210C01.total

theorem join_0_1 : (twinPrimeSegment 440664109 440926253).card = 839 := by
  simpa using combineTwinPrimeSegments (by decide : 440664109 ≤ 440795181)
    (by decide : 440795181 ≤ 440926253) S210C02.total S210C03.total

theorem join_0_2 : (twinPrimeSegment 440926253 441188397).card = 900 := by
  simpa using combineTwinPrimeSegments (by decide : 440926253 ≤ 441057325)
    (by decide : 441057325 ≤ 441188397) S210C04.total S210C05.total

theorem join_0_3 : (twinPrimeSegment 441188397 441450541).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 441188397 ≤ 441319469)
    (by decide : 441319469 ≤ 441450541) S210C06.total S210C07.total

theorem join_0_4 : (twinPrimeSegment 441450541 441712685).card = 808 := by
  simpa using combineTwinPrimeSegments (by decide : 441450541 ≤ 441581613)
    (by decide : 441581613 ≤ 441712685) S210C08.total S210C09.total

theorem join_0_5 : (twinPrimeSegment 441712685 441974829).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 441712685 ≤ 441843757)
    (by decide : 441843757 ≤ 441974829) S210C10.total S210C11.total

theorem join_0_6 : (twinPrimeSegment 441974829 442236973).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 441974829 ≤ 442105901)
    (by decide : 442105901 ≤ 442236973) S210C12.total S210C13.total

theorem join_0_7 : (twinPrimeSegment 442236973 442499117).card = 868 := by
  simpa using combineTwinPrimeSegments (by decide : 442236973 ≤ 442368045)
    (by decide : 442368045 ≤ 442499117) S210C14.total S210C15.total

theorem join_1_0 : (twinPrimeSegment 440401965 440926253).card = 1729 := by
  simpa using combineTwinPrimeSegments (by decide : 440401965 ≤ 440664109)
    (by decide : 440664109 ≤ 440926253) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 440926253 441450541).card = 1790 := by
  simpa using combineTwinPrimeSegments (by decide : 440926253 ≤ 441188397)
    (by decide : 441188397 ≤ 441450541) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 441450541 441974829).card = 1659 := by
  simpa using combineTwinPrimeSegments (by decide : 441450541 ≤ 441712685)
    (by decide : 441712685 ≤ 441974829) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 441974829 442499117).card = 1786 := by
  simpa using combineTwinPrimeSegments (by decide : 441974829 ≤ 442236973)
    (by decide : 442236973 ≤ 442499117) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 440401965 441450541).card = 3519 := by
  simpa using combineTwinPrimeSegments (by decide : 440401965 ≤ 440926253)
    (by decide : 440926253 ≤ 441450541) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 441450541 442499117).card = 3445 := by
  simpa using combineTwinPrimeSegments (by decide : 441450541 ≤ 441974829)
    (by decide : 441974829 ≤ 442499117) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 440401965 442499117).card = 6964 := by
  simpa using combineTwinPrimeSegments (by decide : 440401965 ≤ 441450541)
    (by decide : 441450541 ≤ 442499117) join_2_0 join_2_1

theorem total : (twinPrimeSegment 440401965 442499117).card = 6964 := join_3_0

end S210All
end Sude.GeneratedTwinScan
