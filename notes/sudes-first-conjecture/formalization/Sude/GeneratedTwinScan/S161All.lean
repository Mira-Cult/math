import Sude.GeneratedTwinScan.S161C00
import Sude.GeneratedTwinScan.S161C01
import Sude.GeneratedTwinScan.S161C02
import Sude.GeneratedTwinScan.S161C03
import Sude.GeneratedTwinScan.S161C04
import Sude.GeneratedTwinScan.S161C05
import Sude.GeneratedTwinScan.S161C06
import Sude.GeneratedTwinScan.S161C07
import Sude.GeneratedTwinScan.S161C08
import Sude.GeneratedTwinScan.S161C09
import Sude.GeneratedTwinScan.S161C10
import Sude.GeneratedTwinScan.S161C11
import Sude.GeneratedTwinScan.S161C12
import Sude.GeneratedTwinScan.S161C13
import Sude.GeneratedTwinScan.S161C14
import Sude.GeneratedTwinScan.S161C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S161All

theorem join_0_0 : (twinPrimeSegment 337641517 337903661).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 337641517 ≤ 337772589)
    (by decide : 337772589 ≤ 337903661) S161C00.total S161C01.total

theorem join_0_1 : (twinPrimeSegment 337903661 338165805).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 337903661 ≤ 338034733)
    (by decide : 338034733 ≤ 338165805) S161C02.total S161C03.total

theorem join_0_2 : (twinPrimeSegment 338165805 338427949).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 338165805 ≤ 338296877)
    (by decide : 338296877 ≤ 338427949) S161C04.total S161C05.total

theorem join_0_3 : (twinPrimeSegment 338427949 338690093).card = 921 := by
  simpa using combineTwinPrimeSegments (by decide : 338427949 ≤ 338559021)
    (by decide : 338559021 ≤ 338690093) S161C06.total S161C07.total

theorem join_0_4 : (twinPrimeSegment 338690093 338952237).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 338690093 ≤ 338821165)
    (by decide : 338821165 ≤ 338952237) S161C08.total S161C09.total

theorem join_0_5 : (twinPrimeSegment 338952237 339214381).card = 897 := by
  simpa using combineTwinPrimeSegments (by decide : 338952237 ≤ 339083309)
    (by decide : 339083309 ≤ 339214381) S161C10.total S161C11.total

theorem join_0_6 : (twinPrimeSegment 339214381 339476525).card = 829 := by
  simpa using combineTwinPrimeSegments (by decide : 339214381 ≤ 339345453)
    (by decide : 339345453 ≤ 339476525) S161C12.total S161C13.total

theorem join_0_7 : (twinPrimeSegment 339476525 339738669).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 339476525 ≤ 339607597)
    (by decide : 339607597 ≤ 339738669) S161C14.total S161C15.total

theorem join_1_0 : (twinPrimeSegment 337641517 338165805).card = 1804 := by
  simpa using combineTwinPrimeSegments (by decide : 337641517 ≤ 337903661)
    (by decide : 337903661 ≤ 338165805) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 338165805 338690093).card = 1825 := by
  simpa using combineTwinPrimeSegments (by decide : 338165805 ≤ 338427949)
    (by decide : 338427949 ≤ 338690093) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 338690093 339214381).card = 1762 := by
  simpa using combineTwinPrimeSegments (by decide : 338690093 ≤ 338952237)
    (by decide : 338952237 ≤ 339214381) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 339214381 339738669).card = 1714 := by
  simpa using combineTwinPrimeSegments (by decide : 339214381 ≤ 339476525)
    (by decide : 339476525 ≤ 339738669) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 337641517 338690093).card = 3629 := by
  simpa using combineTwinPrimeSegments (by decide : 337641517 ≤ 338165805)
    (by decide : 338165805 ≤ 338690093) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 338690093 339738669).card = 3476 := by
  simpa using combineTwinPrimeSegments (by decide : 338690093 ≤ 339214381)
    (by decide : 339214381 ≤ 339738669) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 337641517 339738669).card = 7105 := by
  simpa using combineTwinPrimeSegments (by decide : 337641517 ≤ 338690093)
    (by decide : 338690093 ≤ 339738669) join_2_0 join_2_1

theorem total : (twinPrimeSegment 337641517 339738669).card = 7105 := join_3_0

end S161All
end Sude.GeneratedTwinScan
