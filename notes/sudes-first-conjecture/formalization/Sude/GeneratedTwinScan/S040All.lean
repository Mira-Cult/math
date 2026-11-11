import Sude.GeneratedTwinScan.S040C00
import Sude.GeneratedTwinScan.S040C01
import Sude.GeneratedTwinScan.S040C02
import Sude.GeneratedTwinScan.S040C03
import Sude.GeneratedTwinScan.S040C04
import Sude.GeneratedTwinScan.S040C05
import Sude.GeneratedTwinScan.S040C06
import Sude.GeneratedTwinScan.S040C07
import Sude.GeneratedTwinScan.S040C08
import Sude.GeneratedTwinScan.S040C09
import Sude.GeneratedTwinScan.S040C10
import Sude.GeneratedTwinScan.S040C11
import Sude.GeneratedTwinScan.S040C12
import Sude.GeneratedTwinScan.S040C13
import Sude.GeneratedTwinScan.S040C14
import Sude.GeneratedTwinScan.S040C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S040All

theorem join_0_0 : (twinPrimeSegment 83886125 84148269).card = 1064 := by
  simpa using combineTwinPrimeSegments (by decide : 83886125 ≤ 84017197)
    (by decide : 84017197 ≤ 84148269) S040C00.total S040C01.total

theorem join_0_1 : (twinPrimeSegment 84148269 84410413).card = 1048 := by
  simpa using combineTwinPrimeSegments (by decide : 84148269 ≤ 84279341)
    (by decide : 84279341 ≤ 84410413) S040C02.total S040C03.total

theorem join_0_2 : (twinPrimeSegment 84410413 84672557).card = 1074 := by
  simpa using combineTwinPrimeSegments (by decide : 84410413 ≤ 84541485)
    (by decide : 84541485 ≤ 84672557) S040C04.total S040C05.total

theorem join_0_3 : (twinPrimeSegment 84672557 84934701).card = 991 := by
  simpa using combineTwinPrimeSegments (by decide : 84672557 ≤ 84803629)
    (by decide : 84803629 ≤ 84934701) S040C06.total S040C07.total

theorem join_0_4 : (twinPrimeSegment 84934701 85196845).card = 993 := by
  simpa using combineTwinPrimeSegments (by decide : 84934701 ≤ 85065773)
    (by decide : 85065773 ≤ 85196845) S040C08.total S040C09.total

theorem join_0_5 : (twinPrimeSegment 85196845 85458989).card = 1078 := by
  simpa using combineTwinPrimeSegments (by decide : 85196845 ≤ 85327917)
    (by decide : 85327917 ≤ 85458989) S040C10.total S040C11.total

theorem join_0_6 : (twinPrimeSegment 85458989 85721133).card = 1040 := by
  simpa using combineTwinPrimeSegments (by decide : 85458989 ≤ 85590061)
    (by decide : 85590061 ≤ 85721133) S040C12.total S040C13.total

theorem join_0_7 : (twinPrimeSegment 85721133 85983277).card = 1011 := by
  simpa using combineTwinPrimeSegments (by decide : 85721133 ≤ 85852205)
    (by decide : 85852205 ≤ 85983277) S040C14.total S040C15.total

theorem join_1_0 : (twinPrimeSegment 83886125 84410413).card = 2112 := by
  simpa using combineTwinPrimeSegments (by decide : 83886125 ≤ 84148269)
    (by decide : 84148269 ≤ 84410413) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 84410413 84934701).card = 2065 := by
  simpa using combineTwinPrimeSegments (by decide : 84410413 ≤ 84672557)
    (by decide : 84672557 ≤ 84934701) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 84934701 85458989).card = 2071 := by
  simpa using combineTwinPrimeSegments (by decide : 84934701 ≤ 85196845)
    (by decide : 85196845 ≤ 85458989) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 85458989 85983277).card = 2051 := by
  simpa using combineTwinPrimeSegments (by decide : 85458989 ≤ 85721133)
    (by decide : 85721133 ≤ 85983277) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 83886125 84934701).card = 4177 := by
  simpa using combineTwinPrimeSegments (by decide : 83886125 ≤ 84410413)
    (by decide : 84410413 ≤ 84934701) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 84934701 85983277).card = 4122 := by
  simpa using combineTwinPrimeSegments (by decide : 84934701 ≤ 85458989)
    (by decide : 85458989 ≤ 85983277) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 83886125 85983277).card = 8299 := by
  simpa using combineTwinPrimeSegments (by decide : 83886125 ≤ 84934701)
    (by decide : 84934701 ≤ 85983277) join_2_0 join_2_1

theorem total : (twinPrimeSegment 83886125 85983277).card = 8299 := join_3_0

end S040All
end Sude.GeneratedTwinScan
