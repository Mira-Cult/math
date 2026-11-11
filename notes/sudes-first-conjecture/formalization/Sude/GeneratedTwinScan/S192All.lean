import Sude.GeneratedTwinScan.S192C00
import Sude.GeneratedTwinScan.S192C01
import Sude.GeneratedTwinScan.S192C02
import Sude.GeneratedTwinScan.S192C03
import Sude.GeneratedTwinScan.S192C04
import Sude.GeneratedTwinScan.S192C05
import Sude.GeneratedTwinScan.S192C06
import Sude.GeneratedTwinScan.S192C07
import Sude.GeneratedTwinScan.S192C08
import Sude.GeneratedTwinScan.S192C09
import Sude.GeneratedTwinScan.S192C10
import Sude.GeneratedTwinScan.S192C11
import Sude.GeneratedTwinScan.S192C12
import Sude.GeneratedTwinScan.S192C13
import Sude.GeneratedTwinScan.S192C14
import Sude.GeneratedTwinScan.S192C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S192All

theorem join_0_0 : (twinPrimeSegment 402653229 402915373).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 402784301)
    (by decide : 402784301 ≤ 402915373) S192C00.total S192C01.total

theorem join_0_1 : (twinPrimeSegment 402915373 403177517).card = 941 := by
  simpa using combineTwinPrimeSegments (by decide : 402915373 ≤ 403046445)
    (by decide : 403046445 ≤ 403177517) S192C02.total S192C03.total

theorem join_0_2 : (twinPrimeSegment 403177517 403439661).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 403177517 ≤ 403308589)
    (by decide : 403308589 ≤ 403439661) S192C04.total S192C05.total

theorem join_0_3 : (twinPrimeSegment 403439661 403701805).card = 853 := by
  simpa using combineTwinPrimeSegments (by decide : 403439661 ≤ 403570733)
    (by decide : 403570733 ≤ 403701805) S192C06.total S192C07.total

theorem join_0_4 : (twinPrimeSegment 403701805 403963949).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 403701805 ≤ 403832877)
    (by decide : 403832877 ≤ 403963949) S192C08.total S192C09.total

theorem join_0_5 : (twinPrimeSegment 403963949 404226093).card = 895 := by
  simpa using combineTwinPrimeSegments (by decide : 403963949 ≤ 404095021)
    (by decide : 404095021 ≤ 404226093) S192C10.total S192C11.total

theorem join_0_6 : (twinPrimeSegment 404226093 404488237).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 404226093 ≤ 404357165)
    (by decide : 404357165 ≤ 404488237) S192C12.total S192C13.total

theorem join_0_7 : (twinPrimeSegment 404488237 404750381).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 404488237 ≤ 404619309)
    (by decide : 404619309 ≤ 404750381) S192C14.total S192C15.total

theorem join_1_0 : (twinPrimeSegment 402653229 403177517).card = 1804 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 402915373)
    (by decide : 402915373 ≤ 403177517) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 403177517 403701805).card = 1749 := by
  simpa using combineTwinPrimeSegments (by decide : 403177517 ≤ 403439661)
    (by decide : 403439661 ≤ 403701805) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 403701805 404226093).card = 1786 := by
  simpa using combineTwinPrimeSegments (by decide : 403701805 ≤ 403963949)
    (by decide : 403963949 ≤ 404226093) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 404226093 404750381).card = 1736 := by
  simpa using combineTwinPrimeSegments (by decide : 404226093 ≤ 404488237)
    (by decide : 404488237 ≤ 404750381) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 402653229 403701805).card = 3553 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 403177517)
    (by decide : 403177517 ≤ 403701805) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 403701805 404750381).card = 3522 := by
  simpa using combineTwinPrimeSegments (by decide : 403701805 ≤ 404226093)
    (by decide : 404226093 ≤ 404750381) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 402653229 404750381).card = 7075 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 403701805)
    (by decide : 403701805 ≤ 404750381) join_2_0 join_2_1

theorem total : (twinPrimeSegment 402653229 404750381).card = 7075 := join_3_0

end S192All
end Sude.GeneratedTwinScan
