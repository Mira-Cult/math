import Sude.GeneratedTwinScan.S165C00
import Sude.GeneratedTwinScan.S165C01
import Sude.GeneratedTwinScan.S165C02
import Sude.GeneratedTwinScan.S165C03
import Sude.GeneratedTwinScan.S165C04
import Sude.GeneratedTwinScan.S165C05
import Sude.GeneratedTwinScan.S165C06
import Sude.GeneratedTwinScan.S165C07
import Sude.GeneratedTwinScan.S165C08
import Sude.GeneratedTwinScan.S165C09
import Sude.GeneratedTwinScan.S165C10
import Sude.GeneratedTwinScan.S165C11
import Sude.GeneratedTwinScan.S165C12
import Sude.GeneratedTwinScan.S165C13
import Sude.GeneratedTwinScan.S165C14
import Sude.GeneratedTwinScan.S165C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S165All

theorem join_0_0 : (twinPrimeSegment 346030125 346292269).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 346030125 ≤ 346161197)
    (by decide : 346161197 ≤ 346292269) S165C00.total S165C01.total

theorem join_0_1 : (twinPrimeSegment 346292269 346554413).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 346292269 ≤ 346423341)
    (by decide : 346423341 ≤ 346554413) S165C02.total S165C03.total

theorem join_0_2 : (twinPrimeSegment 346554413 346816557).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 346554413 ≤ 346685485)
    (by decide : 346685485 ≤ 346816557) S165C04.total S165C05.total

theorem join_0_3 : (twinPrimeSegment 346816557 347078701).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 346816557 ≤ 346947629)
    (by decide : 346947629 ≤ 347078701) S165C06.total S165C07.total

theorem join_0_4 : (twinPrimeSegment 347078701 347340845).card = 895 := by
  simpa using combineTwinPrimeSegments (by decide : 347078701 ≤ 347209773)
    (by decide : 347209773 ≤ 347340845) S165C08.total S165C09.total

theorem join_0_5 : (twinPrimeSegment 347340845 347602989).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 347340845 ≤ 347471917)
    (by decide : 347471917 ≤ 347602989) S165C10.total S165C11.total

theorem join_0_6 : (twinPrimeSegment 347602989 347865133).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 347602989 ≤ 347734061)
    (by decide : 347734061 ≤ 347865133) S165C12.total S165C13.total

theorem join_0_7 : (twinPrimeSegment 347865133 348127277).card = 886 := by
  simpa using combineTwinPrimeSegments (by decide : 347865133 ≤ 347996205)
    (by decide : 347996205 ≤ 348127277) S165C14.total S165C15.total

theorem join_1_0 : (twinPrimeSegment 346030125 346554413).card = 1733 := by
  simpa using combineTwinPrimeSegments (by decide : 346030125 ≤ 346292269)
    (by decide : 346292269 ≤ 346554413) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 346554413 347078701).card = 1818 := by
  simpa using combineTwinPrimeSegments (by decide : 346554413 ≤ 346816557)
    (by decide : 346816557 ≤ 347078701) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 347078701 347602989).card = 1788 := by
  simpa using combineTwinPrimeSegments (by decide : 347078701 ≤ 347340845)
    (by decide : 347340845 ≤ 347602989) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 347602989 348127277).card = 1789 := by
  simpa using combineTwinPrimeSegments (by decide : 347602989 ≤ 347865133)
    (by decide : 347865133 ≤ 348127277) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 346030125 347078701).card = 3551 := by
  simpa using combineTwinPrimeSegments (by decide : 346030125 ≤ 346554413)
    (by decide : 346554413 ≤ 347078701) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 347078701 348127277).card = 3577 := by
  simpa using combineTwinPrimeSegments (by decide : 347078701 ≤ 347602989)
    (by decide : 347602989 ≤ 348127277) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 346030125 348127277).card = 7128 := by
  simpa using combineTwinPrimeSegments (by decide : 346030125 ≤ 347078701)
    (by decide : 347078701 ≤ 348127277) join_2_0 join_2_1

theorem total : (twinPrimeSegment 346030125 348127277).card = 7128 := join_3_0

end S165All
end Sude.GeneratedTwinScan
