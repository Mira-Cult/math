import Sude.GeneratedTwinScan.S240C00
import Sude.GeneratedTwinScan.S240C01
import Sude.GeneratedTwinScan.S240C02
import Sude.GeneratedTwinScan.S240C03
import Sude.GeneratedTwinScan.S240C04
import Sude.GeneratedTwinScan.S240C05
import Sude.GeneratedTwinScan.S240C06
import Sude.GeneratedTwinScan.S240C07
import Sude.GeneratedTwinScan.S240C08
import Sude.GeneratedTwinScan.S240C09
import Sude.GeneratedTwinScan.S240C10
import Sude.GeneratedTwinScan.S240C11
import Sude.GeneratedTwinScan.S240C12
import Sude.GeneratedTwinScan.S240C13
import Sude.GeneratedTwinScan.S240C14
import Sude.GeneratedTwinScan.S240C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S240All

theorem join_0_0 : (twinPrimeSegment 503316525 503578669).card = 848 := by
  simpa using combineTwinPrimeSegments (by decide : 503316525 ≤ 503447597)
    (by decide : 503447597 ≤ 503578669) S240C00.total S240C01.total

theorem join_0_1 : (twinPrimeSegment 503578669 503840813).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 503578669 ≤ 503709741)
    (by decide : 503709741 ≤ 503840813) S240C02.total S240C03.total

theorem join_0_2 : (twinPrimeSegment 503840813 504102957).card = 856 := by
  simpa using combineTwinPrimeSegments (by decide : 503840813 ≤ 503971885)
    (by decide : 503971885 ≤ 504102957) S240C04.total S240C05.total

theorem join_0_3 : (twinPrimeSegment 504102957 504365101).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 504102957 ≤ 504234029)
    (by decide : 504234029 ≤ 504365101) S240C06.total S240C07.total

theorem join_0_4 : (twinPrimeSegment 504365101 504627245).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 504365101 ≤ 504496173)
    (by decide : 504496173 ≤ 504627245) S240C08.total S240C09.total

theorem join_0_5 : (twinPrimeSegment 504627245 504889389).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 504627245 ≤ 504758317)
    (by decide : 504758317 ≤ 504889389) S240C10.total S240C11.total

theorem join_0_6 : (twinPrimeSegment 504889389 505151533).card = 824 := by
  simpa using combineTwinPrimeSegments (by decide : 504889389 ≤ 505020461)
    (by decide : 505020461 ≤ 505151533) S240C12.total S240C13.total

theorem join_0_7 : (twinPrimeSegment 505151533 505413677).card = 843 := by
  simpa using combineTwinPrimeSegments (by decide : 505151533 ≤ 505282605)
    (by decide : 505282605 ≤ 505413677) S240C14.total S240C15.total

theorem join_1_0 : (twinPrimeSegment 503316525 503840813).card = 1722 := by
  simpa using combineTwinPrimeSegments (by decide : 503316525 ≤ 503578669)
    (by decide : 503578669 ≤ 503840813) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 503840813 504365101).card = 1754 := by
  simpa using combineTwinPrimeSegments (by decide : 503840813 ≤ 504102957)
    (by decide : 504102957 ≤ 504365101) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 504365101 504889389).card = 1733 := by
  simpa using combineTwinPrimeSegments (by decide : 504365101 ≤ 504627245)
    (by decide : 504627245 ≤ 504889389) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 504889389 505413677).card = 1667 := by
  simpa using combineTwinPrimeSegments (by decide : 504889389 ≤ 505151533)
    (by decide : 505151533 ≤ 505413677) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 503316525 504365101).card = 3476 := by
  simpa using combineTwinPrimeSegments (by decide : 503316525 ≤ 503840813)
    (by decide : 503840813 ≤ 504365101) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 504365101 505413677).card = 3400 := by
  simpa using combineTwinPrimeSegments (by decide : 504365101 ≤ 504889389)
    (by decide : 504889389 ≤ 505413677) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 503316525 505413677).card = 6876 := by
  simpa using combineTwinPrimeSegments (by decide : 503316525 ≤ 504365101)
    (by decide : 504365101 ≤ 505413677) join_2_0 join_2_1

theorem total : (twinPrimeSegment 503316525 505413677).card = 6876 := join_3_0

end S240All
end Sude.GeneratedTwinScan
