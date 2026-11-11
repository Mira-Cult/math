import Sude.GeneratedTwinScan.S187C00
import Sude.GeneratedTwinScan.S187C01
import Sude.GeneratedTwinScan.S187C02
import Sude.GeneratedTwinScan.S187C03
import Sude.GeneratedTwinScan.S187C04
import Sude.GeneratedTwinScan.S187C05
import Sude.GeneratedTwinScan.S187C06
import Sude.GeneratedTwinScan.S187C07
import Sude.GeneratedTwinScan.S187C08
import Sude.GeneratedTwinScan.S187C09
import Sude.GeneratedTwinScan.S187C10
import Sude.GeneratedTwinScan.S187C11
import Sude.GeneratedTwinScan.S187C12
import Sude.GeneratedTwinScan.S187C13
import Sude.GeneratedTwinScan.S187C14
import Sude.GeneratedTwinScan.S187C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S187All

theorem join_0_0 : (twinPrimeSegment 392167469 392429613).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 392167469 ≤ 392298541)
    (by decide : 392298541 ≤ 392429613) S187C00.total S187C01.total

theorem join_0_1 : (twinPrimeSegment 392429613 392691757).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 392429613 ≤ 392560685)
    (by decide : 392560685 ≤ 392691757) S187C02.total S187C03.total

theorem join_0_2 : (twinPrimeSegment 392691757 392953901).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 392691757 ≤ 392822829)
    (by decide : 392822829 ≤ 392953901) S187C04.total S187C05.total

theorem join_0_3 : (twinPrimeSegment 392953901 393216045).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 392953901 ≤ 393084973)
    (by decide : 393084973 ≤ 393216045) S187C06.total S187C07.total

theorem join_0_4 : (twinPrimeSegment 393216045 393478189).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 393216045 ≤ 393347117)
    (by decide : 393347117 ≤ 393478189) S187C08.total S187C09.total

theorem join_0_5 : (twinPrimeSegment 393478189 393740333).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 393478189 ≤ 393609261)
    (by decide : 393609261 ≤ 393740333) S187C10.total S187C11.total

theorem join_0_6 : (twinPrimeSegment 393740333 394002477).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 393740333 ≤ 393871405)
    (by decide : 393871405 ≤ 394002477) S187C12.total S187C13.total

theorem join_0_7 : (twinPrimeSegment 394002477 394264621).card = 901 := by
  simpa using combineTwinPrimeSegments (by decide : 394002477 ≤ 394133549)
    (by decide : 394133549 ≤ 394264621) S187C14.total S187C15.total

theorem join_1_0 : (twinPrimeSegment 392167469 392691757).card = 1813 := by
  simpa using combineTwinPrimeSegments (by decide : 392167469 ≤ 392429613)
    (by decide : 392429613 ≤ 392691757) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 392691757 393216045).card = 1726 := by
  simpa using combineTwinPrimeSegments (by decide : 392691757 ≤ 392953901)
    (by decide : 392953901 ≤ 393216045) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 393216045 393740333).card = 1714 := by
  simpa using combineTwinPrimeSegments (by decide : 393216045 ≤ 393478189)
    (by decide : 393478189 ≤ 393740333) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 393740333 394264621).card = 1803 := by
  simpa using combineTwinPrimeSegments (by decide : 393740333 ≤ 394002477)
    (by decide : 394002477 ≤ 394264621) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 392167469 393216045).card = 3539 := by
  simpa using combineTwinPrimeSegments (by decide : 392167469 ≤ 392691757)
    (by decide : 392691757 ≤ 393216045) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 393216045 394264621).card = 3517 := by
  simpa using combineTwinPrimeSegments (by decide : 393216045 ≤ 393740333)
    (by decide : 393740333 ≤ 394264621) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 392167469 394264621).card = 7056 := by
  simpa using combineTwinPrimeSegments (by decide : 392167469 ≤ 393216045)
    (by decide : 393216045 ≤ 394264621) join_2_0 join_2_1

theorem total : (twinPrimeSegment 392167469 394264621).card = 7056 := join_3_0

end S187All
end Sude.GeneratedTwinScan
