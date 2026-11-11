import Sude.GeneratedTwinScan.S107C00
import Sude.GeneratedTwinScan.S107C01
import Sude.GeneratedTwinScan.S107C02
import Sude.GeneratedTwinScan.S107C03
import Sude.GeneratedTwinScan.S107C04
import Sude.GeneratedTwinScan.S107C05
import Sude.GeneratedTwinScan.S107C06
import Sude.GeneratedTwinScan.S107C07
import Sude.GeneratedTwinScan.S107C08
import Sude.GeneratedTwinScan.S107C09
import Sude.GeneratedTwinScan.S107C10
import Sude.GeneratedTwinScan.S107C11
import Sude.GeneratedTwinScan.S107C12
import Sude.GeneratedTwinScan.S107C13
import Sude.GeneratedTwinScan.S107C14
import Sude.GeneratedTwinScan.S107C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S107All

theorem join_0_0 : (twinPrimeSegment 224395309 224657453).card = 940 := by
  simpa using combineTwinPrimeSegments (by decide : 224395309 ≤ 224526381)
    (by decide : 224526381 ≤ 224657453) S107C00.total S107C01.total

theorem join_0_1 : (twinPrimeSegment 224657453 224919597).card = 869 := by
  simpa using combineTwinPrimeSegments (by decide : 224657453 ≤ 224788525)
    (by decide : 224788525 ≤ 224919597) S107C02.total S107C03.total

theorem join_0_2 : (twinPrimeSegment 224919597 225181741).card = 947 := by
  simpa using combineTwinPrimeSegments (by decide : 224919597 ≤ 225050669)
    (by decide : 225050669 ≤ 225181741) S107C04.total S107C05.total

theorem join_0_3 : (twinPrimeSegment 225181741 225443885).card = 872 := by
  simpa using combineTwinPrimeSegments (by decide : 225181741 ≤ 225312813)
    (by decide : 225312813 ≤ 225443885) S107C06.total S107C07.total

theorem join_0_4 : (twinPrimeSegment 225443885 225706029).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 225443885 ≤ 225574957)
    (by decide : 225574957 ≤ 225706029) S107C08.total S107C09.total

theorem join_0_5 : (twinPrimeSegment 225706029 225968173).card = 962 := by
  simpa using combineTwinPrimeSegments (by decide : 225706029 ≤ 225837101)
    (by decide : 225837101 ≤ 225968173) S107C10.total S107C11.total

theorem join_0_6 : (twinPrimeSegment 225968173 226230317).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 225968173 ≤ 226099245)
    (by decide : 226099245 ≤ 226230317) S107C12.total S107C13.total

theorem join_0_7 : (twinPrimeSegment 226230317 226492461).card = 922 := by
  simpa using combineTwinPrimeSegments (by decide : 226230317 ≤ 226361389)
    (by decide : 226361389 ≤ 226492461) S107C14.total S107C15.total

theorem join_1_0 : (twinPrimeSegment 224395309 224919597).card = 1809 := by
  simpa using combineTwinPrimeSegments (by decide : 224395309 ≤ 224657453)
    (by decide : 224657453 ≤ 224919597) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 224919597 225443885).card = 1819 := by
  simpa using combineTwinPrimeSegments (by decide : 224919597 ≤ 225181741)
    (by decide : 225181741 ≤ 225443885) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 225443885 225968173).card = 1874 := by
  simpa using combineTwinPrimeSegments (by decide : 225443885 ≤ 225706029)
    (by decide : 225706029 ≤ 225968173) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 225968173 226492461).card = 1855 := by
  simpa using combineTwinPrimeSegments (by decide : 225968173 ≤ 226230317)
    (by decide : 226230317 ≤ 226492461) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 224395309 225443885).card = 3628 := by
  simpa using combineTwinPrimeSegments (by decide : 224395309 ≤ 224919597)
    (by decide : 224919597 ≤ 225443885) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 225443885 226492461).card = 3729 := by
  simpa using combineTwinPrimeSegments (by decide : 225443885 ≤ 225968173)
    (by decide : 225968173 ≤ 226492461) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 224395309 226492461).card = 7357 := by
  simpa using combineTwinPrimeSegments (by decide : 224395309 ≤ 225443885)
    (by decide : 225443885 ≤ 226492461) join_2_0 join_2_1

theorem total : (twinPrimeSegment 224395309 226492461).card = 7357 := join_3_0

end S107All
end Sude.GeneratedTwinScan
