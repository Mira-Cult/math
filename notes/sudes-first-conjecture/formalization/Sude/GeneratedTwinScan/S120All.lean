import Sude.GeneratedTwinScan.S120C00
import Sude.GeneratedTwinScan.S120C01
import Sude.GeneratedTwinScan.S120C02
import Sude.GeneratedTwinScan.S120C03
import Sude.GeneratedTwinScan.S120C04
import Sude.GeneratedTwinScan.S120C05
import Sude.GeneratedTwinScan.S120C06
import Sude.GeneratedTwinScan.S120C07
import Sude.GeneratedTwinScan.S120C08
import Sude.GeneratedTwinScan.S120C09
import Sude.GeneratedTwinScan.S120C10
import Sude.GeneratedTwinScan.S120C11
import Sude.GeneratedTwinScan.S120C12
import Sude.GeneratedTwinScan.S120C13
import Sude.GeneratedTwinScan.S120C14
import Sude.GeneratedTwinScan.S120C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S120All

theorem join_0_0 : (twinPrimeSegment 251658285 251920429).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 251658285 ≤ 251789357)
    (by decide : 251789357 ≤ 251920429) S120C00.total S120C01.total

theorem join_0_1 : (twinPrimeSegment 251920429 252182573).card = 958 := by
  simpa using combineTwinPrimeSegments (by decide : 251920429 ≤ 252051501)
    (by decide : 252051501 ≤ 252182573) S120C02.total S120C03.total

theorem join_0_2 : (twinPrimeSegment 252182573 252444717).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 252182573 ≤ 252313645)
    (by decide : 252313645 ≤ 252444717) S120C04.total S120C05.total

theorem join_0_3 : (twinPrimeSegment 252444717 252706861).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 252444717 ≤ 252575789)
    (by decide : 252575789 ≤ 252706861) S120C06.total S120C07.total

theorem join_0_4 : (twinPrimeSegment 252706861 252969005).card = 970 := by
  simpa using combineTwinPrimeSegments (by decide : 252706861 ≤ 252837933)
    (by decide : 252837933 ≤ 252969005) S120C08.total S120C09.total

theorem join_0_5 : (twinPrimeSegment 252969005 253231149).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 252969005 ≤ 253100077)
    (by decide : 253100077 ≤ 253231149) S120C10.total S120C11.total

theorem join_0_6 : (twinPrimeSegment 253231149 253493293).card = 937 := by
  simpa using combineTwinPrimeSegments (by decide : 253231149 ≤ 253362221)
    (by decide : 253362221 ≤ 253493293) S120C12.total S120C13.total

theorem join_0_7 : (twinPrimeSegment 253493293 253755437).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 253493293 ≤ 253624365)
    (by decide : 253624365 ≤ 253755437) S120C14.total S120C15.total

theorem join_1_0 : (twinPrimeSegment 251658285 252182573).card = 1847 := by
  simpa using combineTwinPrimeSegments (by decide : 251658285 ≤ 251920429)
    (by decide : 251920429 ≤ 252182573) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 252182573 252706861).card = 1852 := by
  simpa using combineTwinPrimeSegments (by decide : 252182573 ≤ 252444717)
    (by decide : 252444717 ≤ 252706861) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 252706861 253231149).card = 1835 := by
  simpa using combineTwinPrimeSegments (by decide : 252706861 ≤ 252969005)
    (by decide : 252969005 ≤ 253231149) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 253231149 253755437).card = 1879 := by
  simpa using combineTwinPrimeSegments (by decide : 253231149 ≤ 253493293)
    (by decide : 253493293 ≤ 253755437) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 251658285 252706861).card = 3699 := by
  simpa using combineTwinPrimeSegments (by decide : 251658285 ≤ 252182573)
    (by decide : 252182573 ≤ 252706861) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 252706861 253755437).card = 3714 := by
  simpa using combineTwinPrimeSegments (by decide : 252706861 ≤ 253231149)
    (by decide : 253231149 ≤ 253755437) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 251658285 253755437).card = 7413 := by
  simpa using combineTwinPrimeSegments (by decide : 251658285 ≤ 252706861)
    (by decide : 252706861 ≤ 253755437) join_2_0 join_2_1

theorem total : (twinPrimeSegment 251658285 253755437).card = 7413 := join_3_0

end S120All
end Sude.GeneratedTwinScan
