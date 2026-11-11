import Sude.GeneratedTwinScan.S205C00
import Sude.GeneratedTwinScan.S205C01
import Sude.GeneratedTwinScan.S205C02
import Sude.GeneratedTwinScan.S205C03
import Sude.GeneratedTwinScan.S205C04
import Sude.GeneratedTwinScan.S205C05
import Sude.GeneratedTwinScan.S205C06
import Sude.GeneratedTwinScan.S205C07
import Sude.GeneratedTwinScan.S205C08
import Sude.GeneratedTwinScan.S205C09
import Sude.GeneratedTwinScan.S205C10
import Sude.GeneratedTwinScan.S205C11
import Sude.GeneratedTwinScan.S205C12
import Sude.GeneratedTwinScan.S205C13
import Sude.GeneratedTwinScan.S205C14
import Sude.GeneratedTwinScan.S205C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S205All

theorem join_0_0 : (twinPrimeSegment 429916205 430178349).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 429916205 ≤ 430047277)
    (by decide : 430047277 ≤ 430178349) S205C00.total S205C01.total

theorem join_0_1 : (twinPrimeSegment 430178349 430440493).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 430178349 ≤ 430309421)
    (by decide : 430309421 ≤ 430440493) S205C02.total S205C03.total

theorem join_0_2 : (twinPrimeSegment 430440493 430702637).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 430440493 ≤ 430571565)
    (by decide : 430571565 ≤ 430702637) S205C04.total S205C05.total

theorem join_0_3 : (twinPrimeSegment 430702637 430964781).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 430702637 ≤ 430833709)
    (by decide : 430833709 ≤ 430964781) S205C06.total S205C07.total

theorem join_0_4 : (twinPrimeSegment 430964781 431226925).card = 858 := by
  simpa using combineTwinPrimeSegments (by decide : 430964781 ≤ 431095853)
    (by decide : 431095853 ≤ 431226925) S205C08.total S205C09.total

theorem join_0_5 : (twinPrimeSegment 431226925 431489069).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 431226925 ≤ 431357997)
    (by decide : 431357997 ≤ 431489069) S205C10.total S205C11.total

theorem join_0_6 : (twinPrimeSegment 431489069 431751213).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 431489069 ≤ 431620141)
    (by decide : 431620141 ≤ 431751213) S205C12.total S205C13.total

theorem join_0_7 : (twinPrimeSegment 431751213 432013357).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 431751213 ≤ 431882285)
    (by decide : 431882285 ≤ 432013357) S205C14.total S205C15.total

theorem join_1_0 : (twinPrimeSegment 429916205 430440493).card = 1739 := by
  simpa using combineTwinPrimeSegments (by decide : 429916205 ≤ 430178349)
    (by decide : 430178349 ≤ 430440493) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 430440493 430964781).card = 1742 := by
  simpa using combineTwinPrimeSegments (by decide : 430440493 ≤ 430702637)
    (by decide : 430702637 ≤ 430964781) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 430964781 431489069).card = 1722 := by
  simpa using combineTwinPrimeSegments (by decide : 430964781 ≤ 431226925)
    (by decide : 431226925 ≤ 431489069) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 431489069 432013357).card = 1778 := by
  simpa using combineTwinPrimeSegments (by decide : 431489069 ≤ 431751213)
    (by decide : 431751213 ≤ 432013357) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 429916205 430964781).card = 3481 := by
  simpa using combineTwinPrimeSegments (by decide : 429916205 ≤ 430440493)
    (by decide : 430440493 ≤ 430964781) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 430964781 432013357).card = 3500 := by
  simpa using combineTwinPrimeSegments (by decide : 430964781 ≤ 431489069)
    (by decide : 431489069 ≤ 432013357) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 429916205 432013357).card = 6981 := by
  simpa using combineTwinPrimeSegments (by decide : 429916205 ≤ 430964781)
    (by decide : 430964781 ≤ 432013357) join_2_0 join_2_1

theorem total : (twinPrimeSegment 429916205 432013357).card = 6981 := join_3_0

end S205All
end Sude.GeneratedTwinScan
