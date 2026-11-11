import Sude.GeneratedTwinScan.S039C00
import Sude.GeneratedTwinScan.S039C01
import Sude.GeneratedTwinScan.S039C02
import Sude.GeneratedTwinScan.S039C03
import Sude.GeneratedTwinScan.S039C04
import Sude.GeneratedTwinScan.S039C05
import Sude.GeneratedTwinScan.S039C06
import Sude.GeneratedTwinScan.S039C07
import Sude.GeneratedTwinScan.S039C08
import Sude.GeneratedTwinScan.S039C09
import Sude.GeneratedTwinScan.S039C10
import Sude.GeneratedTwinScan.S039C11
import Sude.GeneratedTwinScan.S039C12
import Sude.GeneratedTwinScan.S039C13
import Sude.GeneratedTwinScan.S039C14
import Sude.GeneratedTwinScan.S039C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S039All

theorem join_0_0 : (twinPrimeSegment 81788973 82051117).card = 1041 := by
  simpa using combineTwinPrimeSegments (by decide : 81788973 ≤ 81920045)
    (by decide : 81920045 ≤ 82051117) S039C00.total S039C01.total

theorem join_0_1 : (twinPrimeSegment 82051117 82313261).card = 1045 := by
  simpa using combineTwinPrimeSegments (by decide : 82051117 ≤ 82182189)
    (by decide : 82182189 ≤ 82313261) S039C02.total S039C03.total

theorem join_0_2 : (twinPrimeSegment 82313261 82575405).card = 1040 := by
  simpa using combineTwinPrimeSegments (by decide : 82313261 ≤ 82444333)
    (by decide : 82444333 ≤ 82575405) S039C04.total S039C05.total

theorem join_0_3 : (twinPrimeSegment 82575405 82837549).card = 1042 := by
  simpa using combineTwinPrimeSegments (by decide : 82575405 ≤ 82706477)
    (by decide : 82706477 ≤ 82837549) S039C06.total S039C07.total

theorem join_0_4 : (twinPrimeSegment 82837549 83099693).card = 1020 := by
  simpa using combineTwinPrimeSegments (by decide : 82837549 ≤ 82968621)
    (by decide : 82968621 ≤ 83099693) S039C08.total S039C09.total

theorem join_0_5 : (twinPrimeSegment 83099693 83361837).card = 1033 := by
  simpa using combineTwinPrimeSegments (by decide : 83099693 ≤ 83230765)
    (by decide : 83230765 ≤ 83361837) S039C10.total S039C11.total

theorem join_0_6 : (twinPrimeSegment 83361837 83623981).card = 1032 := by
  simpa using combineTwinPrimeSegments (by decide : 83361837 ≤ 83492909)
    (by decide : 83492909 ≤ 83623981) S039C12.total S039C13.total

theorem join_0_7 : (twinPrimeSegment 83623981 83886125).card = 1064 := by
  simpa using combineTwinPrimeSegments (by decide : 83623981 ≤ 83755053)
    (by decide : 83755053 ≤ 83886125) S039C14.total S039C15.total

theorem join_1_0 : (twinPrimeSegment 81788973 82313261).card = 2086 := by
  simpa using combineTwinPrimeSegments (by decide : 81788973 ≤ 82051117)
    (by decide : 82051117 ≤ 82313261) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 82313261 82837549).card = 2082 := by
  simpa using combineTwinPrimeSegments (by decide : 82313261 ≤ 82575405)
    (by decide : 82575405 ≤ 82837549) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 82837549 83361837).card = 2053 := by
  simpa using combineTwinPrimeSegments (by decide : 82837549 ≤ 83099693)
    (by decide : 83099693 ≤ 83361837) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 83361837 83886125).card = 2096 := by
  simpa using combineTwinPrimeSegments (by decide : 83361837 ≤ 83623981)
    (by decide : 83623981 ≤ 83886125) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 81788973 82837549).card = 4168 := by
  simpa using combineTwinPrimeSegments (by decide : 81788973 ≤ 82313261)
    (by decide : 82313261 ≤ 82837549) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 82837549 83886125).card = 4149 := by
  simpa using combineTwinPrimeSegments (by decide : 82837549 ≤ 83361837)
    (by decide : 83361837 ≤ 83886125) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 81788973 83886125).card = 8317 := by
  simpa using combineTwinPrimeSegments (by decide : 81788973 ≤ 82837549)
    (by decide : 82837549 ≤ 83886125) join_2_0 join_2_1

theorem total : (twinPrimeSegment 81788973 83886125).card = 8317 := join_3_0

end S039All
end Sude.GeneratedTwinScan
