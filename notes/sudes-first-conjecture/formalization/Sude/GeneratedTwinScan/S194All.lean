import Sude.GeneratedTwinScan.S194C00
import Sude.GeneratedTwinScan.S194C01
import Sude.GeneratedTwinScan.S194C02
import Sude.GeneratedTwinScan.S194C03
import Sude.GeneratedTwinScan.S194C04
import Sude.GeneratedTwinScan.S194C05
import Sude.GeneratedTwinScan.S194C06
import Sude.GeneratedTwinScan.S194C07
import Sude.GeneratedTwinScan.S194C08
import Sude.GeneratedTwinScan.S194C09
import Sude.GeneratedTwinScan.S194C10
import Sude.GeneratedTwinScan.S194C11
import Sude.GeneratedTwinScan.S194C12
import Sude.GeneratedTwinScan.S194C13
import Sude.GeneratedTwinScan.S194C14
import Sude.GeneratedTwinScan.S194C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S194All

theorem join_0_0 : (twinPrimeSegment 406847533 407109677).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 406847533 ≤ 406978605)
    (by decide : 406978605 ≤ 407109677) S194C00.total S194C01.total

theorem join_0_1 : (twinPrimeSegment 407109677 407371821).card = 845 := by
  simpa using combineTwinPrimeSegments (by decide : 407109677 ≤ 407240749)
    (by decide : 407240749 ≤ 407371821) S194C02.total S194C03.total

theorem join_0_2 : (twinPrimeSegment 407371821 407633965).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 407371821 ≤ 407502893)
    (by decide : 407502893 ≤ 407633965) S194C04.total S194C05.total

theorem join_0_3 : (twinPrimeSegment 407633965 407896109).card = 884 := by
  simpa using combineTwinPrimeSegments (by decide : 407633965 ≤ 407765037)
    (by decide : 407765037 ≤ 407896109) S194C06.total S194C07.total

theorem join_0_4 : (twinPrimeSegment 407896109 408158253).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 407896109 ≤ 408027181)
    (by decide : 408027181 ≤ 408158253) S194C08.total S194C09.total

theorem join_0_5 : (twinPrimeSegment 408158253 408420397).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 408158253 ≤ 408289325)
    (by decide : 408289325 ≤ 408420397) S194C10.total S194C11.total

theorem join_0_6 : (twinPrimeSegment 408420397 408682541).card = 853 := by
  simpa using combineTwinPrimeSegments (by decide : 408420397 ≤ 408551469)
    (by decide : 408551469 ≤ 408682541) S194C12.total S194C13.total

theorem join_0_7 : (twinPrimeSegment 408682541 408944685).card = 894 := by
  simpa using combineTwinPrimeSegments (by decide : 408682541 ≤ 408813613)
    (by decide : 408813613 ≤ 408944685) S194C14.total S194C15.total

theorem join_1_0 : (twinPrimeSegment 406847533 407371821).card = 1735 := by
  simpa using combineTwinPrimeSegments (by decide : 406847533 ≤ 407109677)
    (by decide : 407109677 ≤ 407371821) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 407371821 407896109).card = 1788 := by
  simpa using combineTwinPrimeSegments (by decide : 407371821 ≤ 407633965)
    (by decide : 407633965 ≤ 407896109) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 407896109 408420397).card = 1768 := by
  simpa using combineTwinPrimeSegments (by decide : 407896109 ≤ 408158253)
    (by decide : 408158253 ≤ 408420397) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 408420397 408944685).card = 1747 := by
  simpa using combineTwinPrimeSegments (by decide : 408420397 ≤ 408682541)
    (by decide : 408682541 ≤ 408944685) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 406847533 407896109).card = 3523 := by
  simpa using combineTwinPrimeSegments (by decide : 406847533 ≤ 407371821)
    (by decide : 407371821 ≤ 407896109) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 407896109 408944685).card = 3515 := by
  simpa using combineTwinPrimeSegments (by decide : 407896109 ≤ 408420397)
    (by decide : 408420397 ≤ 408944685) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 406847533 408944685).card = 7038 := by
  simpa using combineTwinPrimeSegments (by decide : 406847533 ≤ 407896109)
    (by decide : 407896109 ≤ 408944685) join_2_0 join_2_1

theorem total : (twinPrimeSegment 406847533 408944685).card = 7038 := join_3_0

end S194All
end Sude.GeneratedTwinScan
