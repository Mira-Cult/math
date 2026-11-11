import Sude.GeneratedTwinScan.S158C00
import Sude.GeneratedTwinScan.S158C01
import Sude.GeneratedTwinScan.S158C02
import Sude.GeneratedTwinScan.S158C03
import Sude.GeneratedTwinScan.S158C04
import Sude.GeneratedTwinScan.S158C05
import Sude.GeneratedTwinScan.S158C06
import Sude.GeneratedTwinScan.S158C07
import Sude.GeneratedTwinScan.S158C08
import Sude.GeneratedTwinScan.S158C09
import Sude.GeneratedTwinScan.S158C10
import Sude.GeneratedTwinScan.S158C11
import Sude.GeneratedTwinScan.S158C12
import Sude.GeneratedTwinScan.S158C13
import Sude.GeneratedTwinScan.S158C14
import Sude.GeneratedTwinScan.S158C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S158All

theorem join_0_0 : (twinPrimeSegment 331350061 331612205).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 331350061 ≤ 331481133)
    (by decide : 331481133 ≤ 331612205) S158C00.total S158C01.total

theorem join_0_1 : (twinPrimeSegment 331612205 331874349).card = 897 := by
  simpa using combineTwinPrimeSegments (by decide : 331612205 ≤ 331743277)
    (by decide : 331743277 ≤ 331874349) S158C02.total S158C03.total

theorem join_0_2 : (twinPrimeSegment 331874349 332136493).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 331874349 ≤ 332005421)
    (by decide : 332005421 ≤ 332136493) S158C04.total S158C05.total

theorem join_0_3 : (twinPrimeSegment 332136493 332398637).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 332136493 ≤ 332267565)
    (by decide : 332267565 ≤ 332398637) S158C06.total S158C07.total

theorem join_0_4 : (twinPrimeSegment 332398637 332660781).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 332398637 ≤ 332529709)
    (by decide : 332529709 ≤ 332660781) S158C08.total S158C09.total

theorem join_0_5 : (twinPrimeSegment 332660781 332922925).card = 965 := by
  simpa using combineTwinPrimeSegments (by decide : 332660781 ≤ 332791853)
    (by decide : 332791853 ≤ 332922925) S158C10.total S158C11.total

theorem join_0_6 : (twinPrimeSegment 332922925 333185069).card = 911 := by
  simpa using combineTwinPrimeSegments (by decide : 332922925 ≤ 333053997)
    (by decide : 333053997 ≤ 333185069) S158C12.total S158C13.total

theorem join_0_7 : (twinPrimeSegment 333185069 333447213).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 333185069 ≤ 333316141)
    (by decide : 333316141 ≤ 333447213) S158C14.total S158C15.total

theorem join_1_0 : (twinPrimeSegment 331350061 331874349).card = 1771 := by
  simpa using combineTwinPrimeSegments (by decide : 331350061 ≤ 331612205)
    (by decide : 331612205 ≤ 331874349) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 331874349 332398637).card = 1776 := by
  simpa using combineTwinPrimeSegments (by decide : 331874349 ≤ 332136493)
    (by decide : 332136493 ≤ 332398637) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 332398637 332922925).card = 1899 := by
  simpa using combineTwinPrimeSegments (by decide : 332398637 ≤ 332660781)
    (by decide : 332660781 ≤ 332922925) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 332922925 333447213).card = 1800 := by
  simpa using combineTwinPrimeSegments (by decide : 332922925 ≤ 333185069)
    (by decide : 333185069 ≤ 333447213) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 331350061 332398637).card = 3547 := by
  simpa using combineTwinPrimeSegments (by decide : 331350061 ≤ 331874349)
    (by decide : 331874349 ≤ 332398637) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 332398637 333447213).card = 3699 := by
  simpa using combineTwinPrimeSegments (by decide : 332398637 ≤ 332922925)
    (by decide : 332922925 ≤ 333447213) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 331350061 333447213).card = 7246 := by
  simpa using combineTwinPrimeSegments (by decide : 331350061 ≤ 332398637)
    (by decide : 332398637 ≤ 333447213) join_2_0 join_2_1

theorem total : (twinPrimeSegment 331350061 333447213).card = 7246 := join_3_0

end S158All
end Sude.GeneratedTwinScan
