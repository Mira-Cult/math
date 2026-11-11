import Sude.GeneratedTwinScan.S248C00
import Sude.GeneratedTwinScan.S248C01
import Sude.GeneratedTwinScan.S248C02
import Sude.GeneratedTwinScan.S248C03
import Sude.GeneratedTwinScan.S248C04
import Sude.GeneratedTwinScan.S248C05
import Sude.GeneratedTwinScan.S248C06
import Sude.GeneratedTwinScan.S248C07
import Sude.GeneratedTwinScan.S248C08
import Sude.GeneratedTwinScan.S248C09
import Sude.GeneratedTwinScan.S248C10
import Sude.GeneratedTwinScan.S248C11
import Sude.GeneratedTwinScan.S248C12
import Sude.GeneratedTwinScan.S248C13
import Sude.GeneratedTwinScan.S248C14
import Sude.GeneratedTwinScan.S248C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S248All

theorem join_0_0 : (twinPrimeSegment 520093741 520355885).card = 840 := by
  simpa using combineTwinPrimeSegments (by decide : 520093741 ≤ 520224813)
    (by decide : 520224813 ≤ 520355885) S248C00.total S248C01.total

theorem join_0_1 : (twinPrimeSegment 520355885 520618029).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 520355885 ≤ 520486957)
    (by decide : 520486957 ≤ 520618029) S248C02.total S248C03.total

theorem join_0_2 : (twinPrimeSegment 520618029 520880173).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 520618029 ≤ 520749101)
    (by decide : 520749101 ≤ 520880173) S248C04.total S248C05.total

theorem join_0_3 : (twinPrimeSegment 520880173 521142317).card = 833 := by
  simpa using combineTwinPrimeSegments (by decide : 520880173 ≤ 521011245)
    (by decide : 521011245 ≤ 521142317) S248C06.total S248C07.total

theorem join_0_4 : (twinPrimeSegment 521142317 521404461).card = 856 := by
  simpa using combineTwinPrimeSegments (by decide : 521142317 ≤ 521273389)
    (by decide : 521273389 ≤ 521404461) S248C08.total S248C09.total

theorem join_0_5 : (twinPrimeSegment 521404461 521666605).card = 834 := by
  simpa using combineTwinPrimeSegments (by decide : 521404461 ≤ 521535533)
    (by decide : 521535533 ≤ 521666605) S248C10.total S248C11.total

theorem join_0_6 : (twinPrimeSegment 521666605 521928749).card = 854 := by
  simpa using combineTwinPrimeSegments (by decide : 521666605 ≤ 521797677)
    (by decide : 521797677 ≤ 521928749) S248C12.total S248C13.total

theorem join_0_7 : (twinPrimeSegment 521928749 522190893).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 521928749 ≤ 522059821)
    (by decide : 522059821 ≤ 522190893) S248C14.total S248C15.total

theorem join_1_0 : (twinPrimeSegment 520093741 520618029).card = 1701 := by
  simpa using combineTwinPrimeSegments (by decide : 520093741 ≤ 520355885)
    (by decide : 520355885 ≤ 520618029) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 520618029 521142317).card = 1700 := by
  simpa using combineTwinPrimeSegments (by decide : 520618029 ≤ 520880173)
    (by decide : 520880173 ≤ 521142317) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 521142317 521666605).card = 1690 := by
  simpa using combineTwinPrimeSegments (by decide : 521142317 ≤ 521404461)
    (by decide : 521404461 ≤ 521666605) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 521666605 522190893).card = 1733 := by
  simpa using combineTwinPrimeSegments (by decide : 521666605 ≤ 521928749)
    (by decide : 521928749 ≤ 522190893) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 520093741 521142317).card = 3401 := by
  simpa using combineTwinPrimeSegments (by decide : 520093741 ≤ 520618029)
    (by decide : 520618029 ≤ 521142317) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 521142317 522190893).card = 3423 := by
  simpa using combineTwinPrimeSegments (by decide : 521142317 ≤ 521666605)
    (by decide : 521666605 ≤ 522190893) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 520093741 522190893).card = 6824 := by
  simpa using combineTwinPrimeSegments (by decide : 520093741 ≤ 521142317)
    (by decide : 521142317 ≤ 522190893) join_2_0 join_2_1

theorem total : (twinPrimeSegment 520093741 522190893).card = 6824 := join_3_0

end S248All
end Sude.GeneratedTwinScan
