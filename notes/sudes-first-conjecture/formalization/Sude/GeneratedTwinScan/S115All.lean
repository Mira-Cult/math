import Sude.GeneratedTwinScan.S115C00
import Sude.GeneratedTwinScan.S115C01
import Sude.GeneratedTwinScan.S115C02
import Sude.GeneratedTwinScan.S115C03
import Sude.GeneratedTwinScan.S115C04
import Sude.GeneratedTwinScan.S115C05
import Sude.GeneratedTwinScan.S115C06
import Sude.GeneratedTwinScan.S115C07
import Sude.GeneratedTwinScan.S115C08
import Sude.GeneratedTwinScan.S115C09
import Sude.GeneratedTwinScan.S115C10
import Sude.GeneratedTwinScan.S115C11
import Sude.GeneratedTwinScan.S115C12
import Sude.GeneratedTwinScan.S115C13
import Sude.GeneratedTwinScan.S115C14
import Sude.GeneratedTwinScan.S115C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S115All

theorem join_0_0 : (twinPrimeSegment 241172525 241434669).card = 951 := by
  simpa using combineTwinPrimeSegments (by decide : 241172525 ≤ 241303597)
    (by decide : 241303597 ≤ 241434669) S115C00.total S115C01.total

theorem join_0_1 : (twinPrimeSegment 241434669 241696813).card = 960 := by
  simpa using combineTwinPrimeSegments (by decide : 241434669 ≤ 241565741)
    (by decide : 241565741 ≤ 241696813) S115C02.total S115C03.total

theorem join_0_2 : (twinPrimeSegment 241696813 241958957).card = 947 := by
  simpa using combineTwinPrimeSegments (by decide : 241696813 ≤ 241827885)
    (by decide : 241827885 ≤ 241958957) S115C04.total S115C05.total

theorem join_0_3 : (twinPrimeSegment 241958957 242221101).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 241958957 ≤ 242090029)
    (by decide : 242090029 ≤ 242221101) S115C06.total S115C07.total

theorem join_0_4 : (twinPrimeSegment 242221101 242483245).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 242221101 ≤ 242352173)
    (by decide : 242352173 ≤ 242483245) S115C08.total S115C09.total

theorem join_0_5 : (twinPrimeSegment 242483245 242745389).card = 900 := by
  simpa using combineTwinPrimeSegments (by decide : 242483245 ≤ 242614317)
    (by decide : 242614317 ≤ 242745389) S115C10.total S115C11.total

theorem join_0_6 : (twinPrimeSegment 242745389 243007533).card = 951 := by
  simpa using combineTwinPrimeSegments (by decide : 242745389 ≤ 242876461)
    (by decide : 242876461 ≤ 243007533) S115C12.total S115C13.total

theorem join_0_7 : (twinPrimeSegment 243007533 243269677).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 243007533 ≤ 243138605)
    (by decide : 243138605 ≤ 243269677) S115C14.total S115C15.total

theorem join_1_0 : (twinPrimeSegment 241172525 241696813).card = 1911 := by
  simpa using combineTwinPrimeSegments (by decide : 241172525 ≤ 241434669)
    (by decide : 241434669 ≤ 241696813) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 241696813 242221101).card = 1872 := by
  simpa using combineTwinPrimeSegments (by decide : 241696813 ≤ 241958957)
    (by decide : 241958957 ≤ 242221101) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 242221101 242745389).card = 1766 := by
  simpa using combineTwinPrimeSegments (by decide : 242221101 ≤ 242483245)
    (by decide : 242483245 ≤ 242745389) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 242745389 243269677).card = 1876 := by
  simpa using combineTwinPrimeSegments (by decide : 242745389 ≤ 243007533)
    (by decide : 243007533 ≤ 243269677) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 241172525 242221101).card = 3783 := by
  simpa using combineTwinPrimeSegments (by decide : 241172525 ≤ 241696813)
    (by decide : 241696813 ≤ 242221101) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 242221101 243269677).card = 3642 := by
  simpa using combineTwinPrimeSegments (by decide : 242221101 ≤ 242745389)
    (by decide : 242745389 ≤ 243269677) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 241172525 243269677).card = 7425 := by
  simpa using combineTwinPrimeSegments (by decide : 241172525 ≤ 242221101)
    (by decide : 242221101 ≤ 243269677) join_2_0 join_2_1

theorem total : (twinPrimeSegment 241172525 243269677).card = 7425 := join_3_0

end S115All
end Sude.GeneratedTwinScan
