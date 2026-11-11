import Sude.GeneratedTwinScan.S202C00
import Sude.GeneratedTwinScan.S202C01
import Sude.GeneratedTwinScan.S202C02
import Sude.GeneratedTwinScan.S202C03
import Sude.GeneratedTwinScan.S202C04
import Sude.GeneratedTwinScan.S202C05
import Sude.GeneratedTwinScan.S202C06
import Sude.GeneratedTwinScan.S202C07
import Sude.GeneratedTwinScan.S202C08
import Sude.GeneratedTwinScan.S202C09
import Sude.GeneratedTwinScan.S202C10
import Sude.GeneratedTwinScan.S202C11
import Sude.GeneratedTwinScan.S202C12
import Sude.GeneratedTwinScan.S202C13
import Sude.GeneratedTwinScan.S202C14
import Sude.GeneratedTwinScan.S202C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S202All

theorem join_0_0 : (twinPrimeSegment 423624749 423886893).card = 820 := by
  simpa using combineTwinPrimeSegments (by decide : 423624749 ≤ 423755821)
    (by decide : 423755821 ≤ 423886893) S202C00.total S202C01.total

theorem join_0_1 : (twinPrimeSegment 423886893 424149037).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 423886893 ≤ 424017965)
    (by decide : 424017965 ≤ 424149037) S202C02.total S202C03.total

theorem join_0_2 : (twinPrimeSegment 424149037 424411181).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 424149037 ≤ 424280109)
    (by decide : 424280109 ≤ 424411181) S202C04.total S202C05.total

theorem join_0_3 : (twinPrimeSegment 424411181 424673325).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 424411181 ≤ 424542253)
    (by decide : 424542253 ≤ 424673325) S202C06.total S202C07.total

theorem join_0_4 : (twinPrimeSegment 424673325 424935469).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 424673325 ≤ 424804397)
    (by decide : 424804397 ≤ 424935469) S202C08.total S202C09.total

theorem join_0_5 : (twinPrimeSegment 424935469 425197613).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 424935469 ≤ 425066541)
    (by decide : 425066541 ≤ 425197613) S202C10.total S202C11.total

theorem join_0_6 : (twinPrimeSegment 425197613 425459757).card = 894 := by
  simpa using combineTwinPrimeSegments (by decide : 425197613 ≤ 425328685)
    (by decide : 425328685 ≤ 425459757) S202C12.total S202C13.total

theorem join_0_7 : (twinPrimeSegment 425459757 425721901).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 425459757 ≤ 425590829)
    (by decide : 425590829 ≤ 425721901) S202C14.total S202C15.total

theorem join_1_0 : (twinPrimeSegment 423624749 424149037).card = 1696 := by
  simpa using combineTwinPrimeSegments (by decide : 423624749 ≤ 423886893)
    (by decide : 423886893 ≤ 424149037) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 424149037 424673325).card = 1793 := by
  simpa using combineTwinPrimeSegments (by decide : 424149037 ≤ 424411181)
    (by decide : 424411181 ≤ 424673325) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 424673325 425197613).card = 1725 := by
  simpa using combineTwinPrimeSegments (by decide : 424673325 ≤ 424935469)
    (by decide : 424935469 ≤ 425197613) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 425197613 425721901).card = 1777 := by
  simpa using combineTwinPrimeSegments (by decide : 425197613 ≤ 425459757)
    (by decide : 425459757 ≤ 425721901) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 423624749 424673325).card = 3489 := by
  simpa using combineTwinPrimeSegments (by decide : 423624749 ≤ 424149037)
    (by decide : 424149037 ≤ 424673325) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 424673325 425721901).card = 3502 := by
  simpa using combineTwinPrimeSegments (by decide : 424673325 ≤ 425197613)
    (by decide : 425197613 ≤ 425721901) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 423624749 425721901).card = 6991 := by
  simpa using combineTwinPrimeSegments (by decide : 423624749 ≤ 424673325)
    (by decide : 424673325 ≤ 425721901) join_2_0 join_2_1

theorem total : (twinPrimeSegment 423624749 425721901).card = 6991 := join_3_0

end S202All
end Sude.GeneratedTwinScan
