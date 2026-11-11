import Sude.GeneratedTwinScan.S178C00
import Sude.GeneratedTwinScan.S178C01
import Sude.GeneratedTwinScan.S178C02
import Sude.GeneratedTwinScan.S178C03
import Sude.GeneratedTwinScan.S178C04
import Sude.GeneratedTwinScan.S178C05
import Sude.GeneratedTwinScan.S178C06
import Sude.GeneratedTwinScan.S178C07
import Sude.GeneratedTwinScan.S178C08
import Sude.GeneratedTwinScan.S178C09
import Sude.GeneratedTwinScan.S178C10
import Sude.GeneratedTwinScan.S178C11
import Sude.GeneratedTwinScan.S178C12
import Sude.GeneratedTwinScan.S178C13
import Sude.GeneratedTwinScan.S178C14
import Sude.GeneratedTwinScan.S178C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S178All

theorem join_0_0 : (twinPrimeSegment 373293101 373555245).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 373293101 ≤ 373424173)
    (by decide : 373424173 ≤ 373555245) S178C00.total S178C01.total

theorem join_0_1 : (twinPrimeSegment 373555245 373817389).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 373555245 ≤ 373686317)
    (by decide : 373686317 ≤ 373817389) S178C02.total S178C03.total

theorem join_0_2 : (twinPrimeSegment 373817389 374079533).card = 858 := by
  simpa using combineTwinPrimeSegments (by decide : 373817389 ≤ 373948461)
    (by decide : 373948461 ≤ 374079533) S178C04.total S178C05.total

theorem join_0_3 : (twinPrimeSegment 374079533 374341677).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 374079533 ≤ 374210605)
    (by decide : 374210605 ≤ 374341677) S178C06.total S178C07.total

theorem join_0_4 : (twinPrimeSegment 374341677 374603821).card = 940 := by
  simpa using combineTwinPrimeSegments (by decide : 374341677 ≤ 374472749)
    (by decide : 374472749 ≤ 374603821) S178C08.total S178C09.total

theorem join_0_5 : (twinPrimeSegment 374603821 374865965).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 374603821 ≤ 374734893)
    (by decide : 374734893 ≤ 374865965) S178C10.total S178C11.total

theorem join_0_6 : (twinPrimeSegment 374865965 375128109).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 374865965 ≤ 374997037)
    (by decide : 374997037 ≤ 375128109) S178C12.total S178C13.total

theorem join_0_7 : (twinPrimeSegment 375128109 375390253).card = 882 := by
  simpa using combineTwinPrimeSegments (by decide : 375128109 ≤ 375259181)
    (by decide : 375259181 ≤ 375390253) S178C14.total S178C15.total

theorem join_1_0 : (twinPrimeSegment 373293101 373817389).card = 1754 := by
  simpa using combineTwinPrimeSegments (by decide : 373293101 ≤ 373555245)
    (by decide : 373555245 ≤ 373817389) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 373817389 374341677).card = 1764 := by
  simpa using combineTwinPrimeSegments (by decide : 373817389 ≤ 374079533)
    (by decide : 374079533 ≤ 374341677) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 374341677 374865965).card = 1805 := by
  simpa using combineTwinPrimeSegments (by decide : 374341677 ≤ 374603821)
    (by decide : 374603821 ≤ 374865965) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 374865965 375390253).card = 1807 := by
  simpa using combineTwinPrimeSegments (by decide : 374865965 ≤ 375128109)
    (by decide : 375128109 ≤ 375390253) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 373293101 374341677).card = 3518 := by
  simpa using combineTwinPrimeSegments (by decide : 373293101 ≤ 373817389)
    (by decide : 373817389 ≤ 374341677) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 374341677 375390253).card = 3612 := by
  simpa using combineTwinPrimeSegments (by decide : 374341677 ≤ 374865965)
    (by decide : 374865965 ≤ 375390253) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 373293101 375390253).card = 7130 := by
  simpa using combineTwinPrimeSegments (by decide : 373293101 ≤ 374341677)
    (by decide : 374341677 ≤ 375390253) join_2_0 join_2_1

theorem total : (twinPrimeSegment 373293101 375390253).card = 7130 := join_3_0

end S178All
end Sude.GeneratedTwinScan
