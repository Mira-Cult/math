import Sude.GeneratedTwinScan.S234C00
import Sude.GeneratedTwinScan.S234C01
import Sude.GeneratedTwinScan.S234C02
import Sude.GeneratedTwinScan.S234C03
import Sude.GeneratedTwinScan.S234C04
import Sude.GeneratedTwinScan.S234C05
import Sude.GeneratedTwinScan.S234C06
import Sude.GeneratedTwinScan.S234C07
import Sude.GeneratedTwinScan.S234C08
import Sude.GeneratedTwinScan.S234C09
import Sude.GeneratedTwinScan.S234C10
import Sude.GeneratedTwinScan.S234C11
import Sude.GeneratedTwinScan.S234C12
import Sude.GeneratedTwinScan.S234C13
import Sude.GeneratedTwinScan.S234C14
import Sude.GeneratedTwinScan.S234C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S234All

theorem join_0_0 : (twinPrimeSegment 490733613 490995757).card = 855 := by
  simpa using combineTwinPrimeSegments (by decide : 490733613 ≤ 490864685)
    (by decide : 490864685 ≤ 490995757) S234C00.total S234C01.total

theorem join_0_1 : (twinPrimeSegment 490995757 491257901).card = 894 := by
  simpa using combineTwinPrimeSegments (by decide : 490995757 ≤ 491126829)
    (by decide : 491126829 ≤ 491257901) S234C02.total S234C03.total

theorem join_0_2 : (twinPrimeSegment 491257901 491520045).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 491257901 ≤ 491388973)
    (by decide : 491388973 ≤ 491520045) S234C04.total S234C05.total

theorem join_0_3 : (twinPrimeSegment 491520045 491782189).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 491520045 ≤ 491651117)
    (by decide : 491651117 ≤ 491782189) S234C06.total S234C07.total

theorem join_0_4 : (twinPrimeSegment 491782189 492044333).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 491782189 ≤ 491913261)
    (by decide : 491913261 ≤ 492044333) S234C08.total S234C09.total

theorem join_0_5 : (twinPrimeSegment 492044333 492306477).card = 868 := by
  simpa using combineTwinPrimeSegments (by decide : 492044333 ≤ 492175405)
    (by decide : 492175405 ≤ 492306477) S234C10.total S234C11.total

theorem join_0_6 : (twinPrimeSegment 492306477 492568621).card = 853 := by
  simpa using combineTwinPrimeSegments (by decide : 492306477 ≤ 492437549)
    (by decide : 492437549 ≤ 492568621) S234C12.total S234C13.total

theorem join_0_7 : (twinPrimeSegment 492568621 492830765).card = 841 := by
  simpa using combineTwinPrimeSegments (by decide : 492568621 ≤ 492699693)
    (by decide : 492699693 ≤ 492830765) S234C14.total S234C15.total

theorem join_1_0 : (twinPrimeSegment 490733613 491257901).card = 1749 := by
  simpa using combineTwinPrimeSegments (by decide : 490733613 ≤ 490995757)
    (by decide : 490995757 ≤ 491257901) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 491257901 491782189).card = 1752 := by
  simpa using combineTwinPrimeSegments (by decide : 491257901 ≤ 491520045)
    (by decide : 491520045 ≤ 491782189) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 491782189 492306477).card = 1743 := by
  simpa using combineTwinPrimeSegments (by decide : 491782189 ≤ 492044333)
    (by decide : 492044333 ≤ 492306477) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 492306477 492830765).card = 1694 := by
  simpa using combineTwinPrimeSegments (by decide : 492306477 ≤ 492568621)
    (by decide : 492568621 ≤ 492830765) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 490733613 491782189).card = 3501 := by
  simpa using combineTwinPrimeSegments (by decide : 490733613 ≤ 491257901)
    (by decide : 491257901 ≤ 491782189) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 491782189 492830765).card = 3437 := by
  simpa using combineTwinPrimeSegments (by decide : 491782189 ≤ 492306477)
    (by decide : 492306477 ≤ 492830765) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 490733613 492830765).card = 6938 := by
  simpa using combineTwinPrimeSegments (by decide : 490733613 ≤ 491782189)
    (by decide : 491782189 ≤ 492830765) join_2_0 join_2_1

theorem total : (twinPrimeSegment 490733613 492830765).card = 6938 := join_3_0

end S234All
end Sude.GeneratedTwinScan
