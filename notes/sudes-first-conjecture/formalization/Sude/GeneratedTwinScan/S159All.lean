import Sude.GeneratedTwinScan.S159C00
import Sude.GeneratedTwinScan.S159C01
import Sude.GeneratedTwinScan.S159C02
import Sude.GeneratedTwinScan.S159C03
import Sude.GeneratedTwinScan.S159C04
import Sude.GeneratedTwinScan.S159C05
import Sude.GeneratedTwinScan.S159C06
import Sude.GeneratedTwinScan.S159C07
import Sude.GeneratedTwinScan.S159C08
import Sude.GeneratedTwinScan.S159C09
import Sude.GeneratedTwinScan.S159C10
import Sude.GeneratedTwinScan.S159C11
import Sude.GeneratedTwinScan.S159C12
import Sude.GeneratedTwinScan.S159C13
import Sude.GeneratedTwinScan.S159C14
import Sude.GeneratedTwinScan.S159C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S159All

theorem join_0_0 : (twinPrimeSegment 333447213 333709357).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 333447213 ≤ 333578285)
    (by decide : 333578285 ≤ 333709357) S159C00.total S159C01.total

theorem join_0_1 : (twinPrimeSegment 333709357 333971501).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 333709357 ≤ 333840429)
    (by decide : 333840429 ≤ 333971501) S159C02.total S159C03.total

theorem join_0_2 : (twinPrimeSegment 333971501 334233645).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 333971501 ≤ 334102573)
    (by decide : 334102573 ≤ 334233645) S159C04.total S159C05.total

theorem join_0_3 : (twinPrimeSegment 334233645 334495789).card = 935 := by
  simpa using combineTwinPrimeSegments (by decide : 334233645 ≤ 334364717)
    (by decide : 334364717 ≤ 334495789) S159C06.total S159C07.total

theorem join_0_4 : (twinPrimeSegment 334495789 334757933).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 334495789 ≤ 334626861)
    (by decide : 334626861 ≤ 334757933) S159C08.total S159C09.total

theorem join_0_5 : (twinPrimeSegment 334757933 335020077).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 334757933 ≤ 334889005)
    (by decide : 334889005 ≤ 335020077) S159C10.total S159C11.total

theorem join_0_6 : (twinPrimeSegment 335020077 335282221).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 335020077 ≤ 335151149)
    (by decide : 335151149 ≤ 335282221) S159C12.total S159C13.total

theorem join_0_7 : (twinPrimeSegment 335282221 335544365).card = 856 := by
  simpa using combineTwinPrimeSegments (by decide : 335282221 ≤ 335413293)
    (by decide : 335413293 ≤ 335544365) S159C14.total S159C15.total

theorem join_1_0 : (twinPrimeSegment 333447213 333971501).card = 1828 := by
  simpa using combineTwinPrimeSegments (by decide : 333447213 ≤ 333709357)
    (by decide : 333709357 ≤ 333971501) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 333971501 334495789).card = 1853 := by
  simpa using combineTwinPrimeSegments (by decide : 333971501 ≤ 334233645)
    (by decide : 334233645 ≤ 334495789) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 334495789 335020077).card = 1760 := by
  simpa using combineTwinPrimeSegments (by decide : 334495789 ≤ 334757933)
    (by decide : 334757933 ≤ 335020077) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 335020077 335544365).card = 1766 := by
  simpa using combineTwinPrimeSegments (by decide : 335020077 ≤ 335282221)
    (by decide : 335282221 ≤ 335544365) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 333447213 334495789).card = 3681 := by
  simpa using combineTwinPrimeSegments (by decide : 333447213 ≤ 333971501)
    (by decide : 333971501 ≤ 334495789) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 334495789 335544365).card = 3526 := by
  simpa using combineTwinPrimeSegments (by decide : 334495789 ≤ 335020077)
    (by decide : 335020077 ≤ 335544365) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 333447213 335544365).card = 7207 := by
  simpa using combineTwinPrimeSegments (by decide : 333447213 ≤ 334495789)
    (by decide : 334495789 ≤ 335544365) join_2_0 join_2_1

theorem total : (twinPrimeSegment 333447213 335544365).card = 7207 := join_3_0

end S159All
end Sude.GeneratedTwinScan
