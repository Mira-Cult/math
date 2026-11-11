import Sude.GeneratedTwinScan.S239C00
import Sude.GeneratedTwinScan.S239C01
import Sude.GeneratedTwinScan.S239C02
import Sude.GeneratedTwinScan.S239C03
import Sude.GeneratedTwinScan.S239C04
import Sude.GeneratedTwinScan.S239C05
import Sude.GeneratedTwinScan.S239C06
import Sude.GeneratedTwinScan.S239C07
import Sude.GeneratedTwinScan.S239C08
import Sude.GeneratedTwinScan.S239C09
import Sude.GeneratedTwinScan.S239C10
import Sude.GeneratedTwinScan.S239C11
import Sude.GeneratedTwinScan.S239C12
import Sude.GeneratedTwinScan.S239C13
import Sude.GeneratedTwinScan.S239C14
import Sude.GeneratedTwinScan.S239C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S239All

theorem join_0_0 : (twinPrimeSegment 501219373 501481517).card = 845 := by
  simpa using combineTwinPrimeSegments (by decide : 501219373 ≤ 501350445)
    (by decide : 501350445 ≤ 501481517) S239C00.total S239C01.total

theorem join_0_1 : (twinPrimeSegment 501481517 501743661).card = 837 := by
  simpa using combineTwinPrimeSegments (by decide : 501481517 ≤ 501612589)
    (by decide : 501612589 ≤ 501743661) S239C02.total S239C03.total

theorem join_0_2 : (twinPrimeSegment 501743661 502005805).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 501743661 ≤ 501874733)
    (by decide : 501874733 ≤ 502005805) S239C04.total S239C05.total

theorem join_0_3 : (twinPrimeSegment 502005805 502267949).card = 828 := by
  simpa using combineTwinPrimeSegments (by decide : 502005805 ≤ 502136877)
    (by decide : 502136877 ≤ 502267949) S239C06.total S239C07.total

theorem join_0_4 : (twinPrimeSegment 502267949 502530093).card = 858 := by
  simpa using combineTwinPrimeSegments (by decide : 502267949 ≤ 502399021)
    (by decide : 502399021 ≤ 502530093) S239C08.total S239C09.total

theorem join_0_5 : (twinPrimeSegment 502530093 502792237).card = 818 := by
  simpa using combineTwinPrimeSegments (by decide : 502530093 ≤ 502661165)
    (by decide : 502661165 ≤ 502792237) S239C10.total S239C11.total

theorem join_0_6 : (twinPrimeSegment 502792237 503054381).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 502792237 ≤ 502923309)
    (by decide : 502923309 ≤ 503054381) S239C12.total S239C13.total

theorem join_0_7 : (twinPrimeSegment 503054381 503316525).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 503054381 ≤ 503185453)
    (by decide : 503185453 ≤ 503316525) S239C14.total S239C15.total

theorem join_1_0 : (twinPrimeSegment 501219373 501743661).card = 1682 := by
  simpa using combineTwinPrimeSegments (by decide : 501219373 ≤ 501481517)
    (by decide : 501481517 ≤ 501743661) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 501743661 502267949).card = 1707 := by
  simpa using combineTwinPrimeSegments (by decide : 501743661 ≤ 502005805)
    (by decide : 502005805 ≤ 502267949) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 502267949 502792237).card = 1676 := by
  simpa using combineTwinPrimeSegments (by decide : 502267949 ≤ 502530093)
    (by decide : 502530093 ≤ 502792237) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 502792237 503316525).card = 1754 := by
  simpa using combineTwinPrimeSegments (by decide : 502792237 ≤ 503054381)
    (by decide : 503054381 ≤ 503316525) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 501219373 502267949).card = 3389 := by
  simpa using combineTwinPrimeSegments (by decide : 501219373 ≤ 501743661)
    (by decide : 501743661 ≤ 502267949) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 502267949 503316525).card = 3430 := by
  simpa using combineTwinPrimeSegments (by decide : 502267949 ≤ 502792237)
    (by decide : 502792237 ≤ 503316525) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 501219373 503316525).card = 6819 := by
  simpa using combineTwinPrimeSegments (by decide : 501219373 ≤ 502267949)
    (by decide : 502267949 ≤ 503316525) join_2_0 join_2_1

theorem total : (twinPrimeSegment 501219373 503316525).card = 6819 := join_3_0

end S239All
end Sude.GeneratedTwinScan
