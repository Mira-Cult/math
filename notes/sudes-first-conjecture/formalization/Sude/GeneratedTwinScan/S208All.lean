import Sude.GeneratedTwinScan.S208C00
import Sude.GeneratedTwinScan.S208C01
import Sude.GeneratedTwinScan.S208C02
import Sude.GeneratedTwinScan.S208C03
import Sude.GeneratedTwinScan.S208C04
import Sude.GeneratedTwinScan.S208C05
import Sude.GeneratedTwinScan.S208C06
import Sude.GeneratedTwinScan.S208C07
import Sude.GeneratedTwinScan.S208C08
import Sude.GeneratedTwinScan.S208C09
import Sude.GeneratedTwinScan.S208C10
import Sude.GeneratedTwinScan.S208C11
import Sude.GeneratedTwinScan.S208C12
import Sude.GeneratedTwinScan.S208C13
import Sude.GeneratedTwinScan.S208C14
import Sude.GeneratedTwinScan.S208C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S208All

theorem join_0_0 : (twinPrimeSegment 436207661 436469805).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 436207661 ≤ 436338733)
    (by decide : 436338733 ≤ 436469805) S208C00.total S208C01.total

theorem join_0_1 : (twinPrimeSegment 436469805 436731949).card = 853 := by
  simpa using combineTwinPrimeSegments (by decide : 436469805 ≤ 436600877)
    (by decide : 436600877 ≤ 436731949) S208C02.total S208C03.total

theorem join_0_2 : (twinPrimeSegment 436731949 436994093).card = 911 := by
  simpa using combineTwinPrimeSegments (by decide : 436731949 ≤ 436863021)
    (by decide : 436863021 ≤ 436994093) S208C04.total S208C05.total

theorem join_0_3 : (twinPrimeSegment 436994093 437256237).card = 868 := by
  simpa using combineTwinPrimeSegments (by decide : 436994093 ≤ 437125165)
    (by decide : 437125165 ≤ 437256237) S208C06.total S208C07.total

theorem join_0_4 : (twinPrimeSegment 437256237 437518381).card = 846 := by
  simpa using combineTwinPrimeSegments (by decide : 437256237 ≤ 437387309)
    (by decide : 437387309 ≤ 437518381) S208C08.total S208C09.total

theorem join_0_5 : (twinPrimeSegment 437518381 437780525).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 437518381 ≤ 437649453)
    (by decide : 437649453 ≤ 437780525) S208C10.total S208C11.total

theorem join_0_6 : (twinPrimeSegment 437780525 438042669).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 437780525 ≤ 437911597)
    (by decide : 437911597 ≤ 438042669) S208C12.total S208C13.total

theorem join_0_7 : (twinPrimeSegment 438042669 438304813).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 438042669 ≤ 438173741)
    (by decide : 438173741 ≤ 438304813) S208C14.total S208C15.total

theorem join_1_0 : (twinPrimeSegment 436207661 436731949).card = 1729 := by
  simpa using combineTwinPrimeSegments (by decide : 436207661 ≤ 436469805)
    (by decide : 436469805 ≤ 436731949) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 436731949 437256237).card = 1779 := by
  simpa using combineTwinPrimeSegments (by decide : 436731949 ≤ 436994093)
    (by decide : 436994093 ≤ 437256237) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 437256237 437780525).card = 1780 := by
  simpa using combineTwinPrimeSegments (by decide : 437256237 ≤ 437518381)
    (by decide : 437518381 ≤ 437780525) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 437780525 438304813).card = 1780 := by
  simpa using combineTwinPrimeSegments (by decide : 437780525 ≤ 438042669)
    (by decide : 438042669 ≤ 438304813) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 436207661 437256237).card = 3508 := by
  simpa using combineTwinPrimeSegments (by decide : 436207661 ≤ 436731949)
    (by decide : 436731949 ≤ 437256237) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 437256237 438304813).card = 3560 := by
  simpa using combineTwinPrimeSegments (by decide : 437256237 ≤ 437780525)
    (by decide : 437780525 ≤ 438304813) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 436207661 438304813).card = 7068 := by
  simpa using combineTwinPrimeSegments (by decide : 436207661 ≤ 437256237)
    (by decide : 437256237 ≤ 438304813) join_2_0 join_2_1

theorem total : (twinPrimeSegment 436207661 438304813).card = 7068 := join_3_0

end S208All
end Sude.GeneratedTwinScan
