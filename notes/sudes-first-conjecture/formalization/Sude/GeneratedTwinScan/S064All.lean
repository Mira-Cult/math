import Sude.GeneratedTwinScan.S064C00
import Sude.GeneratedTwinScan.S064C01
import Sude.GeneratedTwinScan.S064C02
import Sude.GeneratedTwinScan.S064C03
import Sude.GeneratedTwinScan.S064C04
import Sude.GeneratedTwinScan.S064C05
import Sude.GeneratedTwinScan.S064C06
import Sude.GeneratedTwinScan.S064C07
import Sude.GeneratedTwinScan.S064C08
import Sude.GeneratedTwinScan.S064C09
import Sude.GeneratedTwinScan.S064C10
import Sude.GeneratedTwinScan.S064C11
import Sude.GeneratedTwinScan.S064C12
import Sude.GeneratedTwinScan.S064C13
import Sude.GeneratedTwinScan.S064C14
import Sude.GeneratedTwinScan.S064C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S064All

theorem join_0_0 : (twinPrimeSegment 134217773 134479917).card = 1001 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 134348845)
    (by decide : 134348845 ≤ 134479917) S064C00.total S064C01.total

theorem join_0_1 : (twinPrimeSegment 134479917 134742061).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 134479917 ≤ 134610989)
    (by decide : 134610989 ≤ 134742061) S064C02.total S064C03.total

theorem join_0_2 : (twinPrimeSegment 134742061 135004205).card = 1007 := by
  simpa using combineTwinPrimeSegments (by decide : 134742061 ≤ 134873133)
    (by decide : 134873133 ≤ 135004205) S064C04.total S064C05.total

theorem join_0_3 : (twinPrimeSegment 135004205 135266349).card = 1018 := by
  simpa using combineTwinPrimeSegments (by decide : 135004205 ≤ 135135277)
    (by decide : 135135277 ≤ 135266349) S064C06.total S064C07.total

theorem join_0_4 : (twinPrimeSegment 135266349 135528493).card = 999 := by
  simpa using combineTwinPrimeSegments (by decide : 135266349 ≤ 135397421)
    (by decide : 135397421 ≤ 135528493) S064C08.total S064C09.total

theorem join_0_5 : (twinPrimeSegment 135528493 135790637).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 135528493 ≤ 135659565)
    (by decide : 135659565 ≤ 135790637) S064C10.total S064C11.total

theorem join_0_6 : (twinPrimeSegment 135790637 136052781).card = 1007 := by
  simpa using combineTwinPrimeSegments (by decide : 135790637 ≤ 135921709)
    (by decide : 135921709 ≤ 136052781) S064C12.total S064C13.total

theorem join_0_7 : (twinPrimeSegment 136052781 136314925).card = 976 := by
  simpa using combineTwinPrimeSegments (by decide : 136052781 ≤ 136183853)
    (by decide : 136183853 ≤ 136314925) S064C14.total S064C15.total

theorem join_1_0 : (twinPrimeSegment 134217773 134742061).card = 1930 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 134479917)
    (by decide : 134479917 ≤ 134742061) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 134742061 135266349).card = 2025 := by
  simpa using combineTwinPrimeSegments (by decide : 134742061 ≤ 135004205)
    (by decide : 135004205 ≤ 135266349) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 135266349 135790637).card = 1981 := by
  simpa using combineTwinPrimeSegments (by decide : 135266349 ≤ 135528493)
    (by decide : 135528493 ≤ 135790637) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 135790637 136314925).card = 1983 := by
  simpa using combineTwinPrimeSegments (by decide : 135790637 ≤ 136052781)
    (by decide : 136052781 ≤ 136314925) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 134217773 135266349).card = 3955 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 134742061)
    (by decide : 134742061 ≤ 135266349) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 135266349 136314925).card = 3964 := by
  simpa using combineTwinPrimeSegments (by decide : 135266349 ≤ 135790637)
    (by decide : 135790637 ≤ 136314925) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 134217773 136314925).card = 7919 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 135266349)
    (by decide : 135266349 ≤ 136314925) join_2_0 join_2_1

theorem total : (twinPrimeSegment 134217773 136314925).card = 7919 := join_3_0

end S064All
end Sude.GeneratedTwinScan
