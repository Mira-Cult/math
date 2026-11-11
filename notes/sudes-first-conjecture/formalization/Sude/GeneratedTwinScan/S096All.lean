import Sude.GeneratedTwinScan.S096C00
import Sude.GeneratedTwinScan.S096C01
import Sude.GeneratedTwinScan.S096C02
import Sude.GeneratedTwinScan.S096C03
import Sude.GeneratedTwinScan.S096C04
import Sude.GeneratedTwinScan.S096C05
import Sude.GeneratedTwinScan.S096C06
import Sude.GeneratedTwinScan.S096C07
import Sude.GeneratedTwinScan.S096C08
import Sude.GeneratedTwinScan.S096C09
import Sude.GeneratedTwinScan.S096C10
import Sude.GeneratedTwinScan.S096C11
import Sude.GeneratedTwinScan.S096C12
import Sude.GeneratedTwinScan.S096C13
import Sude.GeneratedTwinScan.S096C14
import Sude.GeneratedTwinScan.S096C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S096All

theorem join_0_0 : (twinPrimeSegment 201326637 201588781).card = 935 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 201457709)
    (by decide : 201457709 ≤ 201588781) S096C00.total S096C01.total

theorem join_0_1 : (twinPrimeSegment 201588781 201850925).card = 928 := by
  simpa using combineTwinPrimeSegments (by decide : 201588781 ≤ 201719853)
    (by decide : 201719853 ≤ 201850925) S096C02.total S096C03.total

theorem join_0_2 : (twinPrimeSegment 201850925 202113069).card = 930 := by
  simpa using combineTwinPrimeSegments (by decide : 201850925 ≤ 201981997)
    (by decide : 201981997 ≤ 202113069) S096C04.total S096C05.total

theorem join_0_3 : (twinPrimeSegment 202113069 202375213).card = 909 := by
  simpa using combineTwinPrimeSegments (by decide : 202113069 ≤ 202244141)
    (by decide : 202244141 ≤ 202375213) S096C06.total S096C07.total

theorem join_0_4 : (twinPrimeSegment 202375213 202637357).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 202375213 ≤ 202506285)
    (by decide : 202506285 ≤ 202637357) S096C08.total S096C09.total

theorem join_0_5 : (twinPrimeSegment 202637357 202899501).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 202637357 ≤ 202768429)
    (by decide : 202768429 ≤ 202899501) S096C10.total S096C11.total

theorem join_0_6 : (twinPrimeSegment 202899501 203161645).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 202899501 ≤ 203030573)
    (by decide : 203030573 ≤ 203161645) S096C12.total S096C13.total

theorem join_0_7 : (twinPrimeSegment 203161645 203423789).card = 946 := by
  simpa using combineTwinPrimeSegments (by decide : 203161645 ≤ 203292717)
    (by decide : 203292717 ≤ 203423789) S096C14.total S096C15.total

theorem join_1_0 : (twinPrimeSegment 201326637 201850925).card = 1863 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 201588781)
    (by decide : 201588781 ≤ 201850925) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 201850925 202375213).card = 1839 := by
  simpa using combineTwinPrimeSegments (by decide : 201850925 ≤ 202113069)
    (by decide : 202113069 ≤ 202375213) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 202375213 202899501).card = 1817 := by
  simpa using combineTwinPrimeSegments (by decide : 202375213 ≤ 202637357)
    (by decide : 202637357 ≤ 202899501) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 202899501 203423789).card = 1921 := by
  simpa using combineTwinPrimeSegments (by decide : 202899501 ≤ 203161645)
    (by decide : 203161645 ≤ 203423789) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 201326637 202375213).card = 3702 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 201850925)
    (by decide : 201850925 ≤ 202375213) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 202375213 203423789).card = 3738 := by
  simpa using combineTwinPrimeSegments (by decide : 202375213 ≤ 202899501)
    (by decide : 202899501 ≤ 203423789) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 201326637 203423789).card = 7440 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 202375213)
    (by decide : 202375213 ≤ 203423789) join_2_0 join_2_1

theorem total : (twinPrimeSegment 201326637 203423789).card = 7440 := join_3_0

end S096All
end Sude.GeneratedTwinScan
