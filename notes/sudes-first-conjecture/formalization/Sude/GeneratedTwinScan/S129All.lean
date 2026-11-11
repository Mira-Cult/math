import Sude.GeneratedTwinScan.S129C00
import Sude.GeneratedTwinScan.S129C01
import Sude.GeneratedTwinScan.S129C02
import Sude.GeneratedTwinScan.S129C03
import Sude.GeneratedTwinScan.S129C04
import Sude.GeneratedTwinScan.S129C05
import Sude.GeneratedTwinScan.S129C06
import Sude.GeneratedTwinScan.S129C07
import Sude.GeneratedTwinScan.S129C08
import Sude.GeneratedTwinScan.S129C09
import Sude.GeneratedTwinScan.S129C10
import Sude.GeneratedTwinScan.S129C11
import Sude.GeneratedTwinScan.S129C12
import Sude.GeneratedTwinScan.S129C13
import Sude.GeneratedTwinScan.S129C14
import Sude.GeneratedTwinScan.S129C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S129All

theorem join_0_0 : (twinPrimeSegment 270532653 270794797).card = 935 := by
  simpa using combineTwinPrimeSegments (by decide : 270532653 ≤ 270663725)
    (by decide : 270663725 ≤ 270794797) S129C00.total S129C01.total

theorem join_0_1 : (twinPrimeSegment 270794797 271056941).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 270794797 ≤ 270925869)
    (by decide : 270925869 ≤ 271056941) S129C02.total S129C03.total

theorem join_0_2 : (twinPrimeSegment 271056941 271319085).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 271056941 ≤ 271188013)
    (by decide : 271188013 ≤ 271319085) S129C04.total S129C05.total

theorem join_0_3 : (twinPrimeSegment 271319085 271581229).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 271319085 ≤ 271450157)
    (by decide : 271450157 ≤ 271581229) S129C06.total S129C07.total

theorem join_0_4 : (twinPrimeSegment 271581229 271843373).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 271581229 ≤ 271712301)
    (by decide : 271712301 ≤ 271843373) S129C08.total S129C09.total

theorem join_0_5 : (twinPrimeSegment 271843373 272105517).card = 953 := by
  simpa using combineTwinPrimeSegments (by decide : 271843373 ≤ 271974445)
    (by decide : 271974445 ≤ 272105517) S129C10.total S129C11.total

theorem join_0_6 : (twinPrimeSegment 272105517 272367661).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 272105517 ≤ 272236589)
    (by decide : 272236589 ≤ 272367661) S129C12.total S129C13.total

theorem join_0_7 : (twinPrimeSegment 272367661 272629805).card = 959 := by
  simpa using combineTwinPrimeSegments (by decide : 272367661 ≤ 272498733)
    (by decide : 272498733 ≤ 272629805) S129C14.total S129C15.total

theorem join_1_0 : (twinPrimeSegment 270532653 271056941).card = 1838 := by
  simpa using combineTwinPrimeSegments (by decide : 270532653 ≤ 270794797)
    (by decide : 270794797 ≤ 271056941) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 271056941 271581229).card = 1806 := by
  simpa using combineTwinPrimeSegments (by decide : 271056941 ≤ 271319085)
    (by decide : 271319085 ≤ 271581229) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 271581229 272105517).card = 1846 := by
  simpa using combineTwinPrimeSegments (by decide : 271581229 ≤ 271843373)
    (by decide : 271843373 ≤ 272105517) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 272105517 272629805).card = 1862 := by
  simpa using combineTwinPrimeSegments (by decide : 272105517 ≤ 272367661)
    (by decide : 272367661 ≤ 272629805) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 270532653 271581229).card = 3644 := by
  simpa using combineTwinPrimeSegments (by decide : 270532653 ≤ 271056941)
    (by decide : 271056941 ≤ 271581229) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 271581229 272629805).card = 3708 := by
  simpa using combineTwinPrimeSegments (by decide : 271581229 ≤ 272105517)
    (by decide : 272105517 ≤ 272629805) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 270532653 272629805).card = 7352 := by
  simpa using combineTwinPrimeSegments (by decide : 270532653 ≤ 271581229)
    (by decide : 271581229 ≤ 272629805) join_2_0 join_2_1

theorem total : (twinPrimeSegment 270532653 272629805).card = 7352 := join_3_0

end S129All
end Sude.GeneratedTwinScan
