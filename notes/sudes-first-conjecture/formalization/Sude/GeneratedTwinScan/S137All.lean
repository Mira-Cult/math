import Sude.GeneratedTwinScan.S137C00
import Sude.GeneratedTwinScan.S137C01
import Sude.GeneratedTwinScan.S137C02
import Sude.GeneratedTwinScan.S137C03
import Sude.GeneratedTwinScan.S137C04
import Sude.GeneratedTwinScan.S137C05
import Sude.GeneratedTwinScan.S137C06
import Sude.GeneratedTwinScan.S137C07
import Sude.GeneratedTwinScan.S137C08
import Sude.GeneratedTwinScan.S137C09
import Sude.GeneratedTwinScan.S137C10
import Sude.GeneratedTwinScan.S137C11
import Sude.GeneratedTwinScan.S137C12
import Sude.GeneratedTwinScan.S137C13
import Sude.GeneratedTwinScan.S137C14
import Sude.GeneratedTwinScan.S137C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S137All

theorem join_0_0 : (twinPrimeSegment 287309869 287572013).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 287309869 ≤ 287440941)
    (by decide : 287440941 ≤ 287572013) S137C00.total S137C01.total

theorem join_0_1 : (twinPrimeSegment 287572013 287834157).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 287572013 ≤ 287703085)
    (by decide : 287703085 ≤ 287834157) S137C02.total S137C03.total

theorem join_0_2 : (twinPrimeSegment 287834157 288096301).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 287834157 ≤ 287965229)
    (by decide : 287965229 ≤ 288096301) S137C04.total S137C05.total

theorem join_0_3 : (twinPrimeSegment 288096301 288358445).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 288096301 ≤ 288227373)
    (by decide : 288227373 ≤ 288358445) S137C06.total S137C07.total

theorem join_0_4 : (twinPrimeSegment 288358445 288620589).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 288358445 ≤ 288489517)
    (by decide : 288489517 ≤ 288620589) S137C08.total S137C09.total

theorem join_0_5 : (twinPrimeSegment 288620589 288882733).card = 949 := by
  simpa using combineTwinPrimeSegments (by decide : 288620589 ≤ 288751661)
    (by decide : 288751661 ≤ 288882733) S137C10.total S137C11.total

theorem join_0_6 : (twinPrimeSegment 288882733 289144877).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 288882733 ≤ 289013805)
    (by decide : 289013805 ≤ 289144877) S137C12.total S137C13.total

theorem join_0_7 : (twinPrimeSegment 289144877 289407021).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 289144877 ≤ 289275949)
    (by decide : 289275949 ≤ 289407021) S137C14.total S137C15.total

theorem join_1_0 : (twinPrimeSegment 287309869 287834157).card = 1819 := by
  simpa using combineTwinPrimeSegments (by decide : 287309869 ≤ 287572013)
    (by decide : 287572013 ≤ 287834157) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 287834157 288358445).card = 1875 := by
  simpa using combineTwinPrimeSegments (by decide : 287834157 ≤ 288096301)
    (by decide : 288096301 ≤ 288358445) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 288358445 288882733).card = 1848 := by
  simpa using combineTwinPrimeSegments (by decide : 288358445 ≤ 288620589)
    (by decide : 288620589 ≤ 288882733) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 288882733 289407021).card = 1841 := by
  simpa using combineTwinPrimeSegments (by decide : 288882733 ≤ 289144877)
    (by decide : 289144877 ≤ 289407021) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 287309869 288358445).card = 3694 := by
  simpa using combineTwinPrimeSegments (by decide : 287309869 ≤ 287834157)
    (by decide : 287834157 ≤ 288358445) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 288358445 289407021).card = 3689 := by
  simpa using combineTwinPrimeSegments (by decide : 288358445 ≤ 288882733)
    (by decide : 288882733 ≤ 289407021) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 287309869 289407021).card = 7383 := by
  simpa using combineTwinPrimeSegments (by decide : 287309869 ≤ 288358445)
    (by decide : 288358445 ≤ 289407021) join_2_0 join_2_1

theorem total : (twinPrimeSegment 287309869 289407021).card = 7383 := join_3_0

end S137All
end Sude.GeneratedTwinScan
