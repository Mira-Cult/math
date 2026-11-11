import Sude.GeneratedTwinScan.S169C00
import Sude.GeneratedTwinScan.S169C01
import Sude.GeneratedTwinScan.S169C02
import Sude.GeneratedTwinScan.S169C03
import Sude.GeneratedTwinScan.S169C04
import Sude.GeneratedTwinScan.S169C05
import Sude.GeneratedTwinScan.S169C06
import Sude.GeneratedTwinScan.S169C07
import Sude.GeneratedTwinScan.S169C08
import Sude.GeneratedTwinScan.S169C09
import Sude.GeneratedTwinScan.S169C10
import Sude.GeneratedTwinScan.S169C11
import Sude.GeneratedTwinScan.S169C12
import Sude.GeneratedTwinScan.S169C13
import Sude.GeneratedTwinScan.S169C14
import Sude.GeneratedTwinScan.S169C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S169All

theorem join_0_0 : (twinPrimeSegment 354418733 354680877).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 354418733 ≤ 354549805)
    (by decide : 354549805 ≤ 354680877) S169C00.total S169C01.total

theorem join_0_1 : (twinPrimeSegment 354680877 354943021).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 354680877 ≤ 354811949)
    (by decide : 354811949 ≤ 354943021) S169C02.total S169C03.total

theorem join_0_2 : (twinPrimeSegment 354943021 355205165).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 354943021 ≤ 355074093)
    (by decide : 355074093 ≤ 355205165) S169C04.total S169C05.total

theorem join_0_3 : (twinPrimeSegment 355205165 355467309).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 355205165 ≤ 355336237)
    (by decide : 355336237 ≤ 355467309) S169C06.total S169C07.total

theorem join_0_4 : (twinPrimeSegment 355467309 355729453).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 355467309 ≤ 355598381)
    (by decide : 355598381 ≤ 355729453) S169C08.total S169C09.total

theorem join_0_5 : (twinPrimeSegment 355729453 355991597).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 355729453 ≤ 355860525)
    (by decide : 355860525 ≤ 355991597) S169C10.total S169C11.total

theorem join_0_6 : (twinPrimeSegment 355991597 356253741).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 355991597 ≤ 356122669)
    (by decide : 356122669 ≤ 356253741) S169C12.total S169C13.total

theorem join_0_7 : (twinPrimeSegment 356253741 356515885).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 356253741 ≤ 356384813)
    (by decide : 356384813 ≤ 356515885) S169C14.total S169C15.total

theorem join_1_0 : (twinPrimeSegment 354418733 354943021).card = 1733 := by
  simpa using combineTwinPrimeSegments (by decide : 354418733 ≤ 354680877)
    (by decide : 354680877 ≤ 354943021) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 354943021 355467309).card = 1852 := by
  simpa using combineTwinPrimeSegments (by decide : 354943021 ≤ 355205165)
    (by decide : 355205165 ≤ 355467309) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 355467309 355991597).card = 1799 := by
  simpa using combineTwinPrimeSegments (by decide : 355467309 ≤ 355729453)
    (by decide : 355729453 ≤ 355991597) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 355991597 356515885).card = 1814 := by
  simpa using combineTwinPrimeSegments (by decide : 355991597 ≤ 356253741)
    (by decide : 356253741 ≤ 356515885) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 354418733 355467309).card = 3585 := by
  simpa using combineTwinPrimeSegments (by decide : 354418733 ≤ 354943021)
    (by decide : 354943021 ≤ 355467309) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 355467309 356515885).card = 3613 := by
  simpa using combineTwinPrimeSegments (by decide : 355467309 ≤ 355991597)
    (by decide : 355991597 ≤ 356515885) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 354418733 356515885).card = 7198 := by
  simpa using combineTwinPrimeSegments (by decide : 354418733 ≤ 355467309)
    (by decide : 355467309 ≤ 356515885) join_2_0 join_2_1

theorem total : (twinPrimeSegment 354418733 356515885).card = 7198 := join_3_0

end S169All
end Sude.GeneratedTwinScan
