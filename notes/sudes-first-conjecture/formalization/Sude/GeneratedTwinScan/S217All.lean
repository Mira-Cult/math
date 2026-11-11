import Sude.GeneratedTwinScan.S217C00
import Sude.GeneratedTwinScan.S217C01
import Sude.GeneratedTwinScan.S217C02
import Sude.GeneratedTwinScan.S217C03
import Sude.GeneratedTwinScan.S217C04
import Sude.GeneratedTwinScan.S217C05
import Sude.GeneratedTwinScan.S217C06
import Sude.GeneratedTwinScan.S217C07
import Sude.GeneratedTwinScan.S217C08
import Sude.GeneratedTwinScan.S217C09
import Sude.GeneratedTwinScan.S217C10
import Sude.GeneratedTwinScan.S217C11
import Sude.GeneratedTwinScan.S217C12
import Sude.GeneratedTwinScan.S217C13
import Sude.GeneratedTwinScan.S217C14
import Sude.GeneratedTwinScan.S217C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S217All

theorem join_0_0 : (twinPrimeSegment 455082029 455344173).card = 944 := by
  simpa using combineTwinPrimeSegments (by decide : 455082029 ≤ 455213101)
    (by decide : 455213101 ≤ 455344173) S217C00.total S217C01.total

theorem join_0_1 : (twinPrimeSegment 455344173 455606317).card = 827 := by
  simpa using combineTwinPrimeSegments (by decide : 455344173 ≤ 455475245)
    (by decide : 455475245 ≤ 455606317) S217C02.total S217C03.total

theorem join_0_2 : (twinPrimeSegment 455606317 455868461).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 455606317 ≤ 455737389)
    (by decide : 455737389 ≤ 455868461) S217C04.total S217C05.total

theorem join_0_3 : (twinPrimeSegment 455868461 456130605).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 455868461 ≤ 455999533)
    (by decide : 455999533 ≤ 456130605) S217C06.total S217C07.total

theorem join_0_4 : (twinPrimeSegment 456130605 456392749).card = 886 := by
  simpa using combineTwinPrimeSegments (by decide : 456130605 ≤ 456261677)
    (by decide : 456261677 ≤ 456392749) S217C08.total S217C09.total

theorem join_0_5 : (twinPrimeSegment 456392749 456654893).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 456392749 ≤ 456523821)
    (by decide : 456523821 ≤ 456654893) S217C10.total S217C11.total

theorem join_0_6 : (twinPrimeSegment 456654893 456917037).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 456654893 ≤ 456785965)
    (by decide : 456785965 ≤ 456917037) S217C12.total S217C13.total

theorem join_0_7 : (twinPrimeSegment 456917037 457179181).card = 818 := by
  simpa using combineTwinPrimeSegments (by decide : 456917037 ≤ 457048109)
    (by decide : 457048109 ≤ 457179181) S217C14.total S217C15.total

theorem join_1_0 : (twinPrimeSegment 455082029 455606317).card = 1771 := by
  simpa using combineTwinPrimeSegments (by decide : 455082029 ≤ 455344173)
    (by decide : 455344173 ≤ 455606317) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 455606317 456130605).card = 1740 := by
  simpa using combineTwinPrimeSegments (by decide : 455606317 ≤ 455868461)
    (by decide : 455868461 ≤ 456130605) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 456130605 456654893).card = 1798 := by
  simpa using combineTwinPrimeSegments (by decide : 456130605 ≤ 456392749)
    (by decide : 456392749 ≤ 456654893) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 456654893 457179181).card = 1706 := by
  simpa using combineTwinPrimeSegments (by decide : 456654893 ≤ 456917037)
    (by decide : 456917037 ≤ 457179181) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 455082029 456130605).card = 3511 := by
  simpa using combineTwinPrimeSegments (by decide : 455082029 ≤ 455606317)
    (by decide : 455606317 ≤ 456130605) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 456130605 457179181).card = 3504 := by
  simpa using combineTwinPrimeSegments (by decide : 456130605 ≤ 456654893)
    (by decide : 456654893 ≤ 457179181) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 455082029 457179181).card = 7015 := by
  simpa using combineTwinPrimeSegments (by decide : 455082029 ≤ 456130605)
    (by decide : 456130605 ≤ 457179181) join_2_0 join_2_1

theorem total : (twinPrimeSegment 455082029 457179181).card = 7015 := join_3_0

end S217All
end Sude.GeneratedTwinScan
