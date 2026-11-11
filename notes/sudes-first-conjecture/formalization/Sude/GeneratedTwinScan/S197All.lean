import Sude.GeneratedTwinScan.S197C00
import Sude.GeneratedTwinScan.S197C01
import Sude.GeneratedTwinScan.S197C02
import Sude.GeneratedTwinScan.S197C03
import Sude.GeneratedTwinScan.S197C04
import Sude.GeneratedTwinScan.S197C05
import Sude.GeneratedTwinScan.S197C06
import Sude.GeneratedTwinScan.S197C07
import Sude.GeneratedTwinScan.S197C08
import Sude.GeneratedTwinScan.S197C09
import Sude.GeneratedTwinScan.S197C10
import Sude.GeneratedTwinScan.S197C11
import Sude.GeneratedTwinScan.S197C12
import Sude.GeneratedTwinScan.S197C13
import Sude.GeneratedTwinScan.S197C14
import Sude.GeneratedTwinScan.S197C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S197All

theorem join_0_0 : (twinPrimeSegment 413138989 413401133).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 413138989 ≤ 413270061)
    (by decide : 413270061 ≤ 413401133) S197C00.total S197C01.total

theorem join_0_1 : (twinPrimeSegment 413401133 413663277).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 413401133 ≤ 413532205)
    (by decide : 413532205 ≤ 413663277) S197C02.total S197C03.total

theorem join_0_2 : (twinPrimeSegment 413663277 413925421).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 413663277 ≤ 413794349)
    (by decide : 413794349 ≤ 413925421) S197C04.total S197C05.total

theorem join_0_3 : (twinPrimeSegment 413925421 414187565).card = 844 := by
  simpa using combineTwinPrimeSegments (by decide : 413925421 ≤ 414056493)
    (by decide : 414056493 ≤ 414187565) S197C06.total S197C07.total

theorem join_0_4 : (twinPrimeSegment 414187565 414449709).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 414187565 ≤ 414318637)
    (by decide : 414318637 ≤ 414449709) S197C08.total S197C09.total

theorem join_0_5 : (twinPrimeSegment 414449709 414711853).card = 868 := by
  simpa using combineTwinPrimeSegments (by decide : 414449709 ≤ 414580781)
    (by decide : 414580781 ≤ 414711853) S197C10.total S197C11.total

theorem join_0_6 : (twinPrimeSegment 414711853 414973997).card = 844 := by
  simpa using combineTwinPrimeSegments (by decide : 414711853 ≤ 414842925)
    (by decide : 414842925 ≤ 414973997) S197C12.total S197C13.total

theorem join_0_7 : (twinPrimeSegment 414973997 415236141).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 414973997 ≤ 415105069)
    (by decide : 415105069 ≤ 415236141) S197C14.total S197C15.total

theorem join_1_0 : (twinPrimeSegment 413138989 413663277).card = 1739 := by
  simpa using combineTwinPrimeSegments (by decide : 413138989 ≤ 413401133)
    (by decide : 413401133 ≤ 413663277) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 413663277 414187565).card = 1727 := by
  simpa using combineTwinPrimeSegments (by decide : 413663277 ≤ 413925421)
    (by decide : 413925421 ≤ 414187565) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 414187565 414711853).card = 1797 := by
  simpa using combineTwinPrimeSegments (by decide : 414187565 ≤ 414449709)
    (by decide : 414449709 ≤ 414711853) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 414711853 415236141).card = 1720 := by
  simpa using combineTwinPrimeSegments (by decide : 414711853 ≤ 414973997)
    (by decide : 414973997 ≤ 415236141) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 413138989 414187565).card = 3466 := by
  simpa using combineTwinPrimeSegments (by decide : 413138989 ≤ 413663277)
    (by decide : 413663277 ≤ 414187565) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 414187565 415236141).card = 3517 := by
  simpa using combineTwinPrimeSegments (by decide : 414187565 ≤ 414711853)
    (by decide : 414711853 ≤ 415236141) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 413138989 415236141).card = 6983 := by
  simpa using combineTwinPrimeSegments (by decide : 413138989 ≤ 414187565)
    (by decide : 414187565 ≤ 415236141) join_2_0 join_2_1

theorem total : (twinPrimeSegment 413138989 415236141).card = 6983 := join_3_0

end S197All
end Sude.GeneratedTwinScan
