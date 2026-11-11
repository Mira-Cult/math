import Sude.GeneratedTwinScan.S249C00
import Sude.GeneratedTwinScan.S249C01
import Sude.GeneratedTwinScan.S249C02
import Sude.GeneratedTwinScan.S249C03
import Sude.GeneratedTwinScan.S249C04
import Sude.GeneratedTwinScan.S249C05
import Sude.GeneratedTwinScan.S249C06
import Sude.GeneratedTwinScan.S249C07
import Sude.GeneratedTwinScan.S249C08
import Sude.GeneratedTwinScan.S249C09
import Sude.GeneratedTwinScan.S249C10
import Sude.GeneratedTwinScan.S249C11
import Sude.GeneratedTwinScan.S249C12
import Sude.GeneratedTwinScan.S249C13
import Sude.GeneratedTwinScan.S249C14
import Sude.GeneratedTwinScan.S249C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S249All

theorem join_0_0 : (twinPrimeSegment 522190893 522453037).card = 841 := by
  simpa using combineTwinPrimeSegments (by decide : 522190893 ≤ 522321965)
    (by decide : 522321965 ≤ 522453037) S249C00.total S249C01.total

theorem join_0_1 : (twinPrimeSegment 522453037 522715181).card = 834 := by
  simpa using combineTwinPrimeSegments (by decide : 522453037 ≤ 522584109)
    (by decide : 522584109 ≤ 522715181) S249C02.total S249C03.total

theorem join_0_2 : (twinPrimeSegment 522715181 522977325).card = 839 := by
  simpa using combineTwinPrimeSegments (by decide : 522715181 ≤ 522846253)
    (by decide : 522846253 ≤ 522977325) S249C04.total S249C05.total

theorem join_0_3 : (twinPrimeSegment 522977325 523239469).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 522977325 ≤ 523108397)
    (by decide : 523108397 ≤ 523239469) S249C06.total S249C07.total

theorem join_0_4 : (twinPrimeSegment 523239469 523501613).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 523239469 ≤ 523370541)
    (by decide : 523370541 ≤ 523501613) S249C08.total S249C09.total

theorem join_0_5 : (twinPrimeSegment 523501613 523763757).card = 838 := by
  simpa using combineTwinPrimeSegments (by decide : 523501613 ≤ 523632685)
    (by decide : 523632685 ≤ 523763757) S249C10.total S249C11.total

theorem join_0_6 : (twinPrimeSegment 523763757 524025901).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 523763757 ≤ 523894829)
    (by decide : 523894829 ≤ 524025901) S249C12.total S249C13.total

theorem join_0_7 : (twinPrimeSegment 524025901 524288045).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 524025901 ≤ 524156973)
    (by decide : 524156973 ≤ 524288045) S249C14.total S249C15.total

theorem join_1_0 : (twinPrimeSegment 522190893 522715181).card = 1675 := by
  simpa using combineTwinPrimeSegments (by decide : 522190893 ≤ 522453037)
    (by decide : 522453037 ≤ 522715181) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 522715181 523239469).card = 1702 := by
  simpa using combineTwinPrimeSegments (by decide : 522715181 ≤ 522977325)
    (by decide : 522977325 ≤ 523239469) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 523239469 523763757).card = 1721 := by
  simpa using combineTwinPrimeSegments (by decide : 523239469 ≤ 523501613)
    (by decide : 523501613 ≤ 523763757) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 523763757 524288045).card = 1753 := by
  simpa using combineTwinPrimeSegments (by decide : 523763757 ≤ 524025901)
    (by decide : 524025901 ≤ 524288045) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 522190893 523239469).card = 3377 := by
  simpa using combineTwinPrimeSegments (by decide : 522190893 ≤ 522715181)
    (by decide : 522715181 ≤ 523239469) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 523239469 524288045).card = 3474 := by
  simpa using combineTwinPrimeSegments (by decide : 523239469 ≤ 523763757)
    (by decide : 523763757 ≤ 524288045) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 522190893 524288045).card = 6851 := by
  simpa using combineTwinPrimeSegments (by decide : 522190893 ≤ 523239469)
    (by decide : 523239469 ≤ 524288045) join_2_0 join_2_1

theorem total : (twinPrimeSegment 522190893 524288045).card = 6851 := join_3_0

end S249All
end Sude.GeneratedTwinScan
