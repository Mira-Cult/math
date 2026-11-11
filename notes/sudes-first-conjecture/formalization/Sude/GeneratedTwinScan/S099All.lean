import Sude.GeneratedTwinScan.S099C00
import Sude.GeneratedTwinScan.S099C01
import Sude.GeneratedTwinScan.S099C02
import Sude.GeneratedTwinScan.S099C03
import Sude.GeneratedTwinScan.S099C04
import Sude.GeneratedTwinScan.S099C05
import Sude.GeneratedTwinScan.S099C06
import Sude.GeneratedTwinScan.S099C07
import Sude.GeneratedTwinScan.S099C08
import Sude.GeneratedTwinScan.S099C09
import Sude.GeneratedTwinScan.S099C10
import Sude.GeneratedTwinScan.S099C11
import Sude.GeneratedTwinScan.S099C12
import Sude.GeneratedTwinScan.S099C13
import Sude.GeneratedTwinScan.S099C14
import Sude.GeneratedTwinScan.S099C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S099All

theorem join_0_0 : (twinPrimeSegment 207618093 207880237).card = 970 := by
  simpa using combineTwinPrimeSegments (by decide : 207618093 ≤ 207749165)
    (by decide : 207749165 ≤ 207880237) S099C00.total S099C01.total

theorem join_0_1 : (twinPrimeSegment 207880237 208142381).card = 938 := by
  simpa using combineTwinPrimeSegments (by decide : 207880237 ≤ 208011309)
    (by decide : 208011309 ≤ 208142381) S099C02.total S099C03.total

theorem join_0_2 : (twinPrimeSegment 208142381 208404525).card = 928 := by
  simpa using combineTwinPrimeSegments (by decide : 208142381 ≤ 208273453)
    (by decide : 208273453 ≤ 208404525) S099C04.total S099C05.total

theorem join_0_3 : (twinPrimeSegment 208404525 208666669).card = 945 := by
  simpa using combineTwinPrimeSegments (by decide : 208404525 ≤ 208535597)
    (by decide : 208535597 ≤ 208666669) S099C06.total S099C07.total

theorem join_0_4 : (twinPrimeSegment 208666669 208928813).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 208666669 ≤ 208797741)
    (by decide : 208797741 ≤ 208928813) S099C08.total S099C09.total

theorem join_0_5 : (twinPrimeSegment 208928813 209190957).card = 931 := by
  simpa using combineTwinPrimeSegments (by decide : 208928813 ≤ 209059885)
    (by decide : 209059885 ≤ 209190957) S099C10.total S099C11.total

theorem join_0_6 : (twinPrimeSegment 209190957 209453101).card = 955 := by
  simpa using combineTwinPrimeSegments (by decide : 209190957 ≤ 209322029)
    (by decide : 209322029 ≤ 209453101) S099C12.total S099C13.total

theorem join_0_7 : (twinPrimeSegment 209453101 209715245).card = 977 := by
  simpa using combineTwinPrimeSegments (by decide : 209453101 ≤ 209584173)
    (by decide : 209584173 ≤ 209715245) S099C14.total S099C15.total

theorem join_1_0 : (twinPrimeSegment 207618093 208142381).card = 1908 := by
  simpa using combineTwinPrimeSegments (by decide : 207618093 ≤ 207880237)
    (by decide : 207880237 ≤ 208142381) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 208142381 208666669).card = 1873 := by
  simpa using combineTwinPrimeSegments (by decide : 208142381 ≤ 208404525)
    (by decide : 208404525 ≤ 208666669) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 208666669 209190957).card = 1906 := by
  simpa using combineTwinPrimeSegments (by decide : 208666669 ≤ 208928813)
    (by decide : 208928813 ≤ 209190957) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 209190957 209715245).card = 1932 := by
  simpa using combineTwinPrimeSegments (by decide : 209190957 ≤ 209453101)
    (by decide : 209453101 ≤ 209715245) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 207618093 208666669).card = 3781 := by
  simpa using combineTwinPrimeSegments (by decide : 207618093 ≤ 208142381)
    (by decide : 208142381 ≤ 208666669) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 208666669 209715245).card = 3838 := by
  simpa using combineTwinPrimeSegments (by decide : 208666669 ≤ 209190957)
    (by decide : 209190957 ≤ 209715245) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 207618093 209715245).card = 7619 := by
  simpa using combineTwinPrimeSegments (by decide : 207618093 ≤ 208666669)
    (by decide : 208666669 ≤ 209715245) join_2_0 join_2_1

theorem total : (twinPrimeSegment 207618093 209715245).card = 7619 := join_3_0

end S099All
end Sude.GeneratedTwinScan
