import Sude.GeneratedTwinScan.S114C00
import Sude.GeneratedTwinScan.S114C01
import Sude.GeneratedTwinScan.S114C02
import Sude.GeneratedTwinScan.S114C03
import Sude.GeneratedTwinScan.S114C04
import Sude.GeneratedTwinScan.S114C05
import Sude.GeneratedTwinScan.S114C06
import Sude.GeneratedTwinScan.S114C07
import Sude.GeneratedTwinScan.S114C08
import Sude.GeneratedTwinScan.S114C09
import Sude.GeneratedTwinScan.S114C10
import Sude.GeneratedTwinScan.S114C11
import Sude.GeneratedTwinScan.S114C12
import Sude.GeneratedTwinScan.S114C13
import Sude.GeneratedTwinScan.S114C14
import Sude.GeneratedTwinScan.S114C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S114All

theorem join_0_0 : (twinPrimeSegment 239075373 239337517).card = 931 := by
  simpa using combineTwinPrimeSegments (by decide : 239075373 ≤ 239206445)
    (by decide : 239206445 ≤ 239337517) S114C00.total S114C01.total

theorem join_0_1 : (twinPrimeSegment 239337517 239599661).card = 991 := by
  simpa using combineTwinPrimeSegments (by decide : 239337517 ≤ 239468589)
    (by decide : 239468589 ≤ 239599661) S114C02.total S114C03.total

theorem join_0_2 : (twinPrimeSegment 239599661 239861805).card = 892 := by
  simpa using combineTwinPrimeSegments (by decide : 239599661 ≤ 239730733)
    (by decide : 239730733 ≤ 239861805) S114C04.total S114C05.total

theorem join_0_3 : (twinPrimeSegment 239861805 240123949).card = 943 := by
  simpa using combineTwinPrimeSegments (by decide : 239861805 ≤ 239992877)
    (by decide : 239992877 ≤ 240123949) S114C06.total S114C07.total

theorem join_0_4 : (twinPrimeSegment 240123949 240386093).card = 969 := by
  simpa using combineTwinPrimeSegments (by decide : 240123949 ≤ 240255021)
    (by decide : 240255021 ≤ 240386093) S114C08.total S114C09.total

theorem join_0_5 : (twinPrimeSegment 240386093 240648237).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 240386093 ≤ 240517165)
    (by decide : 240517165 ≤ 240648237) S114C10.total S114C11.total

theorem join_0_6 : (twinPrimeSegment 240648237 240910381).card = 954 := by
  simpa using combineTwinPrimeSegments (by decide : 240648237 ≤ 240779309)
    (by decide : 240779309 ≤ 240910381) S114C12.total S114C13.total

theorem join_0_7 : (twinPrimeSegment 240910381 241172525).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 240910381 ≤ 241041453)
    (by decide : 241041453 ≤ 241172525) S114C14.total S114C15.total

theorem join_1_0 : (twinPrimeSegment 239075373 239599661).card = 1922 := by
  simpa using combineTwinPrimeSegments (by decide : 239075373 ≤ 239337517)
    (by decide : 239337517 ≤ 239599661) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 239599661 240123949).card = 1835 := by
  simpa using combineTwinPrimeSegments (by decide : 239599661 ≤ 239861805)
    (by decide : 239861805 ≤ 240123949) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 240123949 240648237).card = 1902 := by
  simpa using combineTwinPrimeSegments (by decide : 240123949 ≤ 240386093)
    (by decide : 240386093 ≤ 240648237) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 240648237 241172525).card = 1833 := by
  simpa using combineTwinPrimeSegments (by decide : 240648237 ≤ 240910381)
    (by decide : 240910381 ≤ 241172525) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 239075373 240123949).card = 3757 := by
  simpa using combineTwinPrimeSegments (by decide : 239075373 ≤ 239599661)
    (by decide : 239599661 ≤ 240123949) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 240123949 241172525).card = 3735 := by
  simpa using combineTwinPrimeSegments (by decide : 240123949 ≤ 240648237)
    (by decide : 240648237 ≤ 241172525) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 239075373 241172525).card = 7492 := by
  simpa using combineTwinPrimeSegments (by decide : 239075373 ≤ 240123949)
    (by decide : 240123949 ≤ 241172525) join_2_0 join_2_1

theorem total : (twinPrimeSegment 239075373 241172525).card = 7492 := join_3_0

end S114All
end Sude.GeneratedTwinScan
