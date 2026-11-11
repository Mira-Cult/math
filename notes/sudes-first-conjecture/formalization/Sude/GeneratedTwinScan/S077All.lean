import Sude.GeneratedTwinScan.S077C00
import Sude.GeneratedTwinScan.S077C01
import Sude.GeneratedTwinScan.S077C02
import Sude.GeneratedTwinScan.S077C03
import Sude.GeneratedTwinScan.S077C04
import Sude.GeneratedTwinScan.S077C05
import Sude.GeneratedTwinScan.S077C06
import Sude.GeneratedTwinScan.S077C07
import Sude.GeneratedTwinScan.S077C08
import Sude.GeneratedTwinScan.S077C09
import Sude.GeneratedTwinScan.S077C10
import Sude.GeneratedTwinScan.S077C11
import Sude.GeneratedTwinScan.S077C12
import Sude.GeneratedTwinScan.S077C13
import Sude.GeneratedTwinScan.S077C14
import Sude.GeneratedTwinScan.S077C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S077All

theorem join_0_0 : (twinPrimeSegment 161480749 161742893).card = 944 := by
  simpa using combineTwinPrimeSegments (by decide : 161480749 ≤ 161611821)
    (by decide : 161611821 ≤ 161742893) S077C00.total S077C01.total

theorem join_0_1 : (twinPrimeSegment 161742893 162005037).card = 962 := by
  simpa using combineTwinPrimeSegments (by decide : 161742893 ≤ 161873965)
    (by decide : 161873965 ≤ 162005037) S077C02.total S077C03.total

theorem join_0_2 : (twinPrimeSegment 162005037 162267181).card = 911 := by
  simpa using combineTwinPrimeSegments (by decide : 162005037 ≤ 162136109)
    (by decide : 162136109 ≤ 162267181) S077C04.total S077C05.total

theorem join_0_3 : (twinPrimeSegment 162267181 162529325).card = 957 := by
  simpa using combineTwinPrimeSegments (by decide : 162267181 ≤ 162398253)
    (by decide : 162398253 ≤ 162529325) S077C06.total S077C07.total

theorem join_0_4 : (twinPrimeSegment 162529325 162791469).card = 986 := by
  simpa using combineTwinPrimeSegments (by decide : 162529325 ≤ 162660397)
    (by decide : 162660397 ≤ 162791469) S077C08.total S077C09.total

theorem join_0_5 : (twinPrimeSegment 162791469 163053613).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 162791469 ≤ 162922541)
    (by decide : 162922541 ≤ 163053613) S077C10.total S077C11.total

theorem join_0_6 : (twinPrimeSegment 163053613 163315757).card = 1002 := by
  simpa using combineTwinPrimeSegments (by decide : 163053613 ≤ 163184685)
    (by decide : 163184685 ≤ 163315757) S077C12.total S077C13.total

theorem join_0_7 : (twinPrimeSegment 163315757 163577901).card = 960 := by
  simpa using combineTwinPrimeSegments (by decide : 163315757 ≤ 163446829)
    (by decide : 163446829 ≤ 163577901) S077C14.total S077C15.total

theorem join_1_0 : (twinPrimeSegment 161480749 162005037).card = 1906 := by
  simpa using combineTwinPrimeSegments (by decide : 161480749 ≤ 161742893)
    (by decide : 161742893 ≤ 162005037) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 162005037 162529325).card = 1868 := by
  simpa using combineTwinPrimeSegments (by decide : 162005037 ≤ 162267181)
    (by decide : 162267181 ≤ 162529325) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 162529325 163053613).card = 1915 := by
  simpa using combineTwinPrimeSegments (by decide : 162529325 ≤ 162791469)
    (by decide : 162791469 ≤ 163053613) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 163053613 163577901).card = 1962 := by
  simpa using combineTwinPrimeSegments (by decide : 163053613 ≤ 163315757)
    (by decide : 163315757 ≤ 163577901) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 161480749 162529325).card = 3774 := by
  simpa using combineTwinPrimeSegments (by decide : 161480749 ≤ 162005037)
    (by decide : 162005037 ≤ 162529325) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 162529325 163577901).card = 3877 := by
  simpa using combineTwinPrimeSegments (by decide : 162529325 ≤ 163053613)
    (by decide : 163053613 ≤ 163577901) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 161480749 163577901).card = 7651 := by
  simpa using combineTwinPrimeSegments (by decide : 161480749 ≤ 162529325)
    (by decide : 162529325 ≤ 163577901) join_2_0 join_2_1

theorem total : (twinPrimeSegment 161480749 163577901).card = 7651 := join_3_0

end S077All
end Sude.GeneratedTwinScan
