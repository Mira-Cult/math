import Sude.GeneratedTwinScan.S047C00
import Sude.GeneratedTwinScan.S047C01
import Sude.GeneratedTwinScan.S047C02
import Sude.GeneratedTwinScan.S047C03
import Sude.GeneratedTwinScan.S047C04
import Sude.GeneratedTwinScan.S047C05
import Sude.GeneratedTwinScan.S047C06
import Sude.GeneratedTwinScan.S047C07
import Sude.GeneratedTwinScan.S047C08
import Sude.GeneratedTwinScan.S047C09
import Sude.GeneratedTwinScan.S047C10
import Sude.GeneratedTwinScan.S047C11
import Sude.GeneratedTwinScan.S047C12
import Sude.GeneratedTwinScan.S047C13
import Sude.GeneratedTwinScan.S047C14
import Sude.GeneratedTwinScan.S047C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S047All

theorem join_0_0 : (twinPrimeSegment 98566189 98828333).card = 1038 := by
  simpa using combineTwinPrimeSegments (by decide : 98566189 ≤ 98697261)
    (by decide : 98697261 ≤ 98828333) S047C00.total S047C01.total

theorem join_0_1 : (twinPrimeSegment 98828333 99090477).card = 1009 := by
  simpa using combineTwinPrimeSegments (by decide : 98828333 ≤ 98959405)
    (by decide : 98959405 ≤ 99090477) S047C02.total S047C03.total

theorem join_0_2 : (twinPrimeSegment 99090477 99352621).card = 1027 := by
  simpa using combineTwinPrimeSegments (by decide : 99090477 ≤ 99221549)
    (by decide : 99221549 ≤ 99352621) S047C04.total S047C05.total

theorem join_0_3 : (twinPrimeSegment 99352621 99614765).card = 1048 := by
  simpa using combineTwinPrimeSegments (by decide : 99352621 ≤ 99483693)
    (by decide : 99483693 ≤ 99614765) S047C06.total S047C07.total

theorem join_0_4 : (twinPrimeSegment 99614765 99876909).card = 1005 := by
  simpa using combineTwinPrimeSegments (by decide : 99614765 ≤ 99745837)
    (by decide : 99745837 ≤ 99876909) S047C08.total S047C09.total

theorem join_0_5 : (twinPrimeSegment 99876909 100139053).card = 1049 := by
  simpa using combineTwinPrimeSegments (by decide : 99876909 ≤ 100007981)
    (by decide : 100007981 ≤ 100139053) S047C10.total S047C11.total

theorem join_0_6 : (twinPrimeSegment 100139053 100401197).card = 1006 := by
  simpa using combineTwinPrimeSegments (by decide : 100139053 ≤ 100270125)
    (by decide : 100270125 ≤ 100401197) S047C12.total S047C13.total

theorem join_0_7 : (twinPrimeSegment 100401197 100663341).card = 1039 := by
  simpa using combineTwinPrimeSegments (by decide : 100401197 ≤ 100532269)
    (by decide : 100532269 ≤ 100663341) S047C14.total S047C15.total

theorem join_1_0 : (twinPrimeSegment 98566189 99090477).card = 2047 := by
  simpa using combineTwinPrimeSegments (by decide : 98566189 ≤ 98828333)
    (by decide : 98828333 ≤ 99090477) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 99090477 99614765).card = 2075 := by
  simpa using combineTwinPrimeSegments (by decide : 99090477 ≤ 99352621)
    (by decide : 99352621 ≤ 99614765) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 99614765 100139053).card = 2054 := by
  simpa using combineTwinPrimeSegments (by decide : 99614765 ≤ 99876909)
    (by decide : 99876909 ≤ 100139053) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 100139053 100663341).card = 2045 := by
  simpa using combineTwinPrimeSegments (by decide : 100139053 ≤ 100401197)
    (by decide : 100401197 ≤ 100663341) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 98566189 99614765).card = 4122 := by
  simpa using combineTwinPrimeSegments (by decide : 98566189 ≤ 99090477)
    (by decide : 99090477 ≤ 99614765) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 99614765 100663341).card = 4099 := by
  simpa using combineTwinPrimeSegments (by decide : 99614765 ≤ 100139053)
    (by decide : 100139053 ≤ 100663341) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 98566189 100663341).card = 8221 := by
  simpa using combineTwinPrimeSegments (by decide : 98566189 ≤ 99614765)
    (by decide : 99614765 ≤ 100663341) join_2_0 join_2_1

theorem total : (twinPrimeSegment 98566189 100663341).card = 8221 := join_3_0

end S047All
end Sude.GeneratedTwinScan
