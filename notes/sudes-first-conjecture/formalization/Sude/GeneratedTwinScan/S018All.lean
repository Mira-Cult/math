import Sude.GeneratedTwinScan.S018C00
import Sude.GeneratedTwinScan.S018C01
import Sude.GeneratedTwinScan.S018C02
import Sude.GeneratedTwinScan.S018C03
import Sude.GeneratedTwinScan.S018C04
import Sude.GeneratedTwinScan.S018C05
import Sude.GeneratedTwinScan.S018C06
import Sude.GeneratedTwinScan.S018C07
import Sude.GeneratedTwinScan.S018C08
import Sude.GeneratedTwinScan.S018C09
import Sude.GeneratedTwinScan.S018C10
import Sude.GeneratedTwinScan.S018C11
import Sude.GeneratedTwinScan.S018C12
import Sude.GeneratedTwinScan.S018C13
import Sude.GeneratedTwinScan.S018C14
import Sude.GeneratedTwinScan.S018C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S018All

theorem join_0_0 : (twinPrimeSegment 37748781 38010925).card = 1130 := by
  simpa using combineTwinPrimeSegments (by decide : 37748781 ≤ 37879853)
    (by decide : 37879853 ≤ 38010925) S018C00.total S018C01.total

theorem join_0_1 : (twinPrimeSegment 38010925 38273069).card = 1192 := by
  simpa using combineTwinPrimeSegments (by decide : 38010925 ≤ 38141997)
    (by decide : 38141997 ≤ 38273069) S018C02.total S018C03.total

theorem join_0_2 : (twinPrimeSegment 38273069 38535213).card = 1101 := by
  simpa using combineTwinPrimeSegments (by decide : 38273069 ≤ 38404141)
    (by decide : 38404141 ≤ 38535213) S018C04.total S018C05.total

theorem join_0_3 : (twinPrimeSegment 38535213 38797357).card = 1126 := by
  simpa using combineTwinPrimeSegments (by decide : 38535213 ≤ 38666285)
    (by decide : 38666285 ≤ 38797357) S018C06.total S018C07.total

theorem join_0_4 : (twinPrimeSegment 38797357 39059501).card = 1103 := by
  simpa using combineTwinPrimeSegments (by decide : 38797357 ≤ 38928429)
    (by decide : 38928429 ≤ 39059501) S018C08.total S018C09.total

theorem join_0_5 : (twinPrimeSegment 39059501 39321645).card = 1111 := by
  simpa using combineTwinPrimeSegments (by decide : 39059501 ≤ 39190573)
    (by decide : 39190573 ≤ 39321645) S018C10.total S018C11.total

theorem join_0_6 : (twinPrimeSegment 39321645 39583789).card = 1183 := by
  simpa using combineTwinPrimeSegments (by decide : 39321645 ≤ 39452717)
    (by decide : 39452717 ≤ 39583789) S018C12.total S018C13.total

theorem join_0_7 : (twinPrimeSegment 39583789 39845933).card = 1175 := by
  simpa using combineTwinPrimeSegments (by decide : 39583789 ≤ 39714861)
    (by decide : 39714861 ≤ 39845933) S018C14.total S018C15.total

theorem join_1_0 : (twinPrimeSegment 37748781 38273069).card = 2322 := by
  simpa using combineTwinPrimeSegments (by decide : 37748781 ≤ 38010925)
    (by decide : 38010925 ≤ 38273069) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 38273069 38797357).card = 2227 := by
  simpa using combineTwinPrimeSegments (by decide : 38273069 ≤ 38535213)
    (by decide : 38535213 ≤ 38797357) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 38797357 39321645).card = 2214 := by
  simpa using combineTwinPrimeSegments (by decide : 38797357 ≤ 39059501)
    (by decide : 39059501 ≤ 39321645) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 39321645 39845933).card = 2358 := by
  simpa using combineTwinPrimeSegments (by decide : 39321645 ≤ 39583789)
    (by decide : 39583789 ≤ 39845933) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 37748781 38797357).card = 4549 := by
  simpa using combineTwinPrimeSegments (by decide : 37748781 ≤ 38273069)
    (by decide : 38273069 ≤ 38797357) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 38797357 39845933).card = 4572 := by
  simpa using combineTwinPrimeSegments (by decide : 38797357 ≤ 39321645)
    (by decide : 39321645 ≤ 39845933) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 37748781 39845933).card = 9121 := by
  simpa using combineTwinPrimeSegments (by decide : 37748781 ≤ 38797357)
    (by decide : 38797357 ≤ 39845933) join_2_0 join_2_1

theorem total : (twinPrimeSegment 37748781 39845933).card = 9121 := join_3_0

end S018All
end Sude.GeneratedTwinScan
