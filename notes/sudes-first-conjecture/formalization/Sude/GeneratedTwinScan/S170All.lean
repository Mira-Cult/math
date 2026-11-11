import Sude.GeneratedTwinScan.S170C00
import Sude.GeneratedTwinScan.S170C01
import Sude.GeneratedTwinScan.S170C02
import Sude.GeneratedTwinScan.S170C03
import Sude.GeneratedTwinScan.S170C04
import Sude.GeneratedTwinScan.S170C05
import Sude.GeneratedTwinScan.S170C06
import Sude.GeneratedTwinScan.S170C07
import Sude.GeneratedTwinScan.S170C08
import Sude.GeneratedTwinScan.S170C09
import Sude.GeneratedTwinScan.S170C10
import Sude.GeneratedTwinScan.S170C11
import Sude.GeneratedTwinScan.S170C12
import Sude.GeneratedTwinScan.S170C13
import Sude.GeneratedTwinScan.S170C14
import Sude.GeneratedTwinScan.S170C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S170All

theorem join_0_0 : (twinPrimeSegment 356515885 356778029).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 356515885 ≤ 356646957)
    (by decide : 356646957 ≤ 356778029) S170C00.total S170C01.total

theorem join_0_1 : (twinPrimeSegment 356778029 357040173).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 356778029 ≤ 356909101)
    (by decide : 356909101 ≤ 357040173) S170C02.total S170C03.total

theorem join_0_2 : (twinPrimeSegment 357040173 357302317).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 357040173 ≤ 357171245)
    (by decide : 357171245 ≤ 357302317) S170C04.total S170C05.total

theorem join_0_3 : (twinPrimeSegment 357302317 357564461).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 357302317 ≤ 357433389)
    (by decide : 357433389 ≤ 357564461) S170C06.total S170C07.total

theorem join_0_4 : (twinPrimeSegment 357564461 357826605).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 357564461 ≤ 357695533)
    (by decide : 357695533 ≤ 357826605) S170C08.total S170C09.total

theorem join_0_5 : (twinPrimeSegment 357826605 358088749).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 357826605 ≤ 357957677)
    (by decide : 357957677 ≤ 358088749) S170C10.total S170C11.total

theorem join_0_6 : (twinPrimeSegment 358088749 358350893).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 358088749 ≤ 358219821)
    (by decide : 358219821 ≤ 358350893) S170C12.total S170C13.total

theorem join_0_7 : (twinPrimeSegment 358350893 358613037).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 358350893 ≤ 358481965)
    (by decide : 358481965 ≤ 358613037) S170C14.total S170C15.total

theorem join_1_0 : (twinPrimeSegment 356515885 357040173).card = 1749 := by
  simpa using combineTwinPrimeSegments (by decide : 356515885 ≤ 356778029)
    (by decide : 356778029 ≤ 357040173) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 357040173 357564461).card = 1790 := by
  simpa using combineTwinPrimeSegments (by decide : 357040173 ≤ 357302317)
    (by decide : 357302317 ≤ 357564461) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 357564461 358088749).card = 1749 := by
  simpa using combineTwinPrimeSegments (by decide : 357564461 ≤ 357826605)
    (by decide : 357826605 ≤ 358088749) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 358088749 358613037).card = 1767 := by
  simpa using combineTwinPrimeSegments (by decide : 358088749 ≤ 358350893)
    (by decide : 358350893 ≤ 358613037) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 356515885 357564461).card = 3539 := by
  simpa using combineTwinPrimeSegments (by decide : 356515885 ≤ 357040173)
    (by decide : 357040173 ≤ 357564461) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 357564461 358613037).card = 3516 := by
  simpa using combineTwinPrimeSegments (by decide : 357564461 ≤ 358088749)
    (by decide : 358088749 ≤ 358613037) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 356515885 358613037).card = 7055 := by
  simpa using combineTwinPrimeSegments (by decide : 356515885 ≤ 357564461)
    (by decide : 357564461 ≤ 358613037) join_2_0 join_2_1

theorem total : (twinPrimeSegment 356515885 358613037).card = 7055 := join_3_0

end S170All
end Sude.GeneratedTwinScan
