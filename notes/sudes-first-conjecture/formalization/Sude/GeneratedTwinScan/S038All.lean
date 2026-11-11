import Sude.GeneratedTwinScan.S038C00
import Sude.GeneratedTwinScan.S038C01
import Sude.GeneratedTwinScan.S038C02
import Sude.GeneratedTwinScan.S038C03
import Sude.GeneratedTwinScan.S038C04
import Sude.GeneratedTwinScan.S038C05
import Sude.GeneratedTwinScan.S038C06
import Sude.GeneratedTwinScan.S038C07
import Sude.GeneratedTwinScan.S038C08
import Sude.GeneratedTwinScan.S038C09
import Sude.GeneratedTwinScan.S038C10
import Sude.GeneratedTwinScan.S038C11
import Sude.GeneratedTwinScan.S038C12
import Sude.GeneratedTwinScan.S038C13
import Sude.GeneratedTwinScan.S038C14
import Sude.GeneratedTwinScan.S038C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S038All

theorem join_0_0 : (twinPrimeSegment 79691821 79953965).card = 1041 := by
  simpa using combineTwinPrimeSegments (by decide : 79691821 ≤ 79822893)
    (by decide : 79822893 ≤ 79953965) S038C00.total S038C01.total

theorem join_0_1 : (twinPrimeSegment 79953965 80216109).card = 1026 := by
  simpa using combineTwinPrimeSegments (by decide : 79953965 ≤ 80085037)
    (by decide : 80085037 ≤ 80216109) S038C02.total S038C03.total

theorem join_0_2 : (twinPrimeSegment 80216109 80478253).card = 1042 := by
  simpa using combineTwinPrimeSegments (by decide : 80216109 ≤ 80347181)
    (by decide : 80347181 ≤ 80478253) S038C04.total S038C05.total

theorem join_0_3 : (twinPrimeSegment 80478253 80740397).card = 1026 := by
  simpa using combineTwinPrimeSegments (by decide : 80478253 ≤ 80609325)
    (by decide : 80609325 ≤ 80740397) S038C06.total S038C07.total

theorem join_0_4 : (twinPrimeSegment 80740397 81002541).card = 1010 := by
  simpa using combineTwinPrimeSegments (by decide : 80740397 ≤ 80871469)
    (by decide : 80871469 ≤ 81002541) S038C08.total S038C09.total

theorem join_0_5 : (twinPrimeSegment 81002541 81264685).card = 1095 := by
  simpa using combineTwinPrimeSegments (by decide : 81002541 ≤ 81133613)
    (by decide : 81133613 ≤ 81264685) S038C10.total S038C11.total

theorem join_0_6 : (twinPrimeSegment 81264685 81526829).card = 1069 := by
  simpa using combineTwinPrimeSegments (by decide : 81264685 ≤ 81395757)
    (by decide : 81395757 ≤ 81526829) S038C12.total S038C13.total

theorem join_0_7 : (twinPrimeSegment 81526829 81788973).card = 1050 := by
  simpa using combineTwinPrimeSegments (by decide : 81526829 ≤ 81657901)
    (by decide : 81657901 ≤ 81788973) S038C14.total S038C15.total

theorem join_1_0 : (twinPrimeSegment 79691821 80216109).card = 2067 := by
  simpa using combineTwinPrimeSegments (by decide : 79691821 ≤ 79953965)
    (by decide : 79953965 ≤ 80216109) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 80216109 80740397).card = 2068 := by
  simpa using combineTwinPrimeSegments (by decide : 80216109 ≤ 80478253)
    (by decide : 80478253 ≤ 80740397) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 80740397 81264685).card = 2105 := by
  simpa using combineTwinPrimeSegments (by decide : 80740397 ≤ 81002541)
    (by decide : 81002541 ≤ 81264685) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 81264685 81788973).card = 2119 := by
  simpa using combineTwinPrimeSegments (by decide : 81264685 ≤ 81526829)
    (by decide : 81526829 ≤ 81788973) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 79691821 80740397).card = 4135 := by
  simpa using combineTwinPrimeSegments (by decide : 79691821 ≤ 80216109)
    (by decide : 80216109 ≤ 80740397) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 80740397 81788973).card = 4224 := by
  simpa using combineTwinPrimeSegments (by decide : 80740397 ≤ 81264685)
    (by decide : 81264685 ≤ 81788973) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 79691821 81788973).card = 8359 := by
  simpa using combineTwinPrimeSegments (by decide : 79691821 ≤ 80740397)
    (by decide : 80740397 ≤ 81788973) join_2_0 join_2_1

theorem total : (twinPrimeSegment 79691821 81788973).card = 8359 := join_3_0

end S038All
end Sude.GeneratedTwinScan
