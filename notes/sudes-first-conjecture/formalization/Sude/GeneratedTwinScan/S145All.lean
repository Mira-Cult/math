import Sude.GeneratedTwinScan.S145C00
import Sude.GeneratedTwinScan.S145C01
import Sude.GeneratedTwinScan.S145C02
import Sude.GeneratedTwinScan.S145C03
import Sude.GeneratedTwinScan.S145C04
import Sude.GeneratedTwinScan.S145C05
import Sude.GeneratedTwinScan.S145C06
import Sude.GeneratedTwinScan.S145C07
import Sude.GeneratedTwinScan.S145C08
import Sude.GeneratedTwinScan.S145C09
import Sude.GeneratedTwinScan.S145C10
import Sude.GeneratedTwinScan.S145C11
import Sude.GeneratedTwinScan.S145C12
import Sude.GeneratedTwinScan.S145C13
import Sude.GeneratedTwinScan.S145C14
import Sude.GeneratedTwinScan.S145C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S145All

theorem join_0_0 : (twinPrimeSegment 304087085 304349229).card = 927 := by
  simpa using combineTwinPrimeSegments (by decide : 304087085 ≤ 304218157)
    (by decide : 304218157 ≤ 304349229) S145C00.total S145C01.total

theorem join_0_1 : (twinPrimeSegment 304349229 304611373).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 304349229 ≤ 304480301)
    (by decide : 304480301 ≤ 304611373) S145C02.total S145C03.total

theorem join_0_2 : (twinPrimeSegment 304611373 304873517).card = 955 := by
  simpa using combineTwinPrimeSegments (by decide : 304611373 ≤ 304742445)
    (by decide : 304742445 ≤ 304873517) S145C04.total S145C05.total

theorem join_0_3 : (twinPrimeSegment 304873517 305135661).card = 949 := by
  simpa using combineTwinPrimeSegments (by decide : 304873517 ≤ 305004589)
    (by decide : 305004589 ≤ 305135661) S145C06.total S145C07.total

theorem join_0_4 : (twinPrimeSegment 305135661 305397805).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 305135661 ≤ 305266733)
    (by decide : 305266733 ≤ 305397805) S145C08.total S145C09.total

theorem join_0_5 : (twinPrimeSegment 305397805 305659949).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 305397805 ≤ 305528877)
    (by decide : 305528877 ≤ 305659949) S145C10.total S145C11.total

theorem join_0_6 : (twinPrimeSegment 305659949 305922093).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 305659949 ≤ 305791021)
    (by decide : 305791021 ≤ 305922093) S145C12.total S145C13.total

theorem join_0_7 : (twinPrimeSegment 305922093 306184237).card = 938 := by
  simpa using combineTwinPrimeSegments (by decide : 305922093 ≤ 306053165)
    (by decide : 306053165 ≤ 306184237) S145C14.total S145C15.total

theorem join_1_0 : (twinPrimeSegment 304087085 304611373).card = 1860 := by
  simpa using combineTwinPrimeSegments (by decide : 304087085 ≤ 304349229)
    (by decide : 304349229 ≤ 304611373) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 304611373 305135661).card = 1904 := by
  simpa using combineTwinPrimeSegments (by decide : 304611373 ≤ 304873517)
    (by decide : 304873517 ≤ 305135661) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 305135661 305659949).card = 1798 := by
  simpa using combineTwinPrimeSegments (by decide : 305135661 ≤ 305397805)
    (by decide : 305397805 ≤ 305659949) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 305659949 306184237).card = 1827 := by
  simpa using combineTwinPrimeSegments (by decide : 305659949 ≤ 305922093)
    (by decide : 305922093 ≤ 306184237) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 304087085 305135661).card = 3764 := by
  simpa using combineTwinPrimeSegments (by decide : 304087085 ≤ 304611373)
    (by decide : 304611373 ≤ 305135661) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 305135661 306184237).card = 3625 := by
  simpa using combineTwinPrimeSegments (by decide : 305135661 ≤ 305659949)
    (by decide : 305659949 ≤ 306184237) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 304087085 306184237).card = 7389 := by
  simpa using combineTwinPrimeSegments (by decide : 304087085 ≤ 305135661)
    (by decide : 305135661 ≤ 306184237) join_2_0 join_2_1

theorem total : (twinPrimeSegment 304087085 306184237).card = 7389 := join_3_0

end S145All
end Sude.GeneratedTwinScan
