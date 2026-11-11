import Sude.GeneratedTwinScan.S030C00
import Sude.GeneratedTwinScan.S030C01
import Sude.GeneratedTwinScan.S030C02
import Sude.GeneratedTwinScan.S030C03
import Sude.GeneratedTwinScan.S030C04
import Sude.GeneratedTwinScan.S030C05
import Sude.GeneratedTwinScan.S030C06
import Sude.GeneratedTwinScan.S030C07
import Sude.GeneratedTwinScan.S030C08
import Sude.GeneratedTwinScan.S030C09
import Sude.GeneratedTwinScan.S030C10
import Sude.GeneratedTwinScan.S030C11
import Sude.GeneratedTwinScan.S030C12
import Sude.GeneratedTwinScan.S030C13
import Sude.GeneratedTwinScan.S030C14
import Sude.GeneratedTwinScan.S030C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S030All

theorem join_0_0 : (twinPrimeSegment 62914605 63176749).card = 1102 := by
  simpa using combineTwinPrimeSegments (by decide : 62914605 ≤ 63045677)
    (by decide : 63045677 ≤ 63176749) S030C00.total S030C01.total

theorem join_0_1 : (twinPrimeSegment 63176749 63438893).card = 1075 := by
  simpa using combineTwinPrimeSegments (by decide : 63176749 ≤ 63307821)
    (by decide : 63307821 ≤ 63438893) S030C02.total S030C03.total

theorem join_0_2 : (twinPrimeSegment 63438893 63701037).card = 1086 := by
  simpa using combineTwinPrimeSegments (by decide : 63438893 ≤ 63569965)
    (by decide : 63569965 ≤ 63701037) S030C04.total S030C05.total

theorem join_0_3 : (twinPrimeSegment 63701037 63963181).card = 1091 := by
  simpa using combineTwinPrimeSegments (by decide : 63701037 ≤ 63832109)
    (by decide : 63832109 ≤ 63963181) S030C06.total S030C07.total

theorem join_0_4 : (twinPrimeSegment 63963181 64225325).card = 1061 := by
  simpa using combineTwinPrimeSegments (by decide : 63963181 ≤ 64094253)
    (by decide : 64094253 ≤ 64225325) S030C08.total S030C09.total

theorem join_0_5 : (twinPrimeSegment 64225325 64487469).card = 1083 := by
  simpa using combineTwinPrimeSegments (by decide : 64225325 ≤ 64356397)
    (by decide : 64356397 ≤ 64487469) S030C10.total S030C11.total

theorem join_0_6 : (twinPrimeSegment 64487469 64749613).card = 1026 := by
  simpa using combineTwinPrimeSegments (by decide : 64487469 ≤ 64618541)
    (by decide : 64618541 ≤ 64749613) S030C12.total S030C13.total

theorem join_0_7 : (twinPrimeSegment 64749613 65011757).card = 1078 := by
  simpa using combineTwinPrimeSegments (by decide : 64749613 ≤ 64880685)
    (by decide : 64880685 ≤ 65011757) S030C14.total S030C15.total

theorem join_1_0 : (twinPrimeSegment 62914605 63438893).card = 2177 := by
  simpa using combineTwinPrimeSegments (by decide : 62914605 ≤ 63176749)
    (by decide : 63176749 ≤ 63438893) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 63438893 63963181).card = 2177 := by
  simpa using combineTwinPrimeSegments (by decide : 63438893 ≤ 63701037)
    (by decide : 63701037 ≤ 63963181) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 63963181 64487469).card = 2144 := by
  simpa using combineTwinPrimeSegments (by decide : 63963181 ≤ 64225325)
    (by decide : 64225325 ≤ 64487469) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 64487469 65011757).card = 2104 := by
  simpa using combineTwinPrimeSegments (by decide : 64487469 ≤ 64749613)
    (by decide : 64749613 ≤ 65011757) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 62914605 63963181).card = 4354 := by
  simpa using combineTwinPrimeSegments (by decide : 62914605 ≤ 63438893)
    (by decide : 63438893 ≤ 63963181) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 63963181 65011757).card = 4248 := by
  simpa using combineTwinPrimeSegments (by decide : 63963181 ≤ 64487469)
    (by decide : 64487469 ≤ 65011757) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 62914605 65011757).card = 8602 := by
  simpa using combineTwinPrimeSegments (by decide : 62914605 ≤ 63963181)
    (by decide : 63963181 ≤ 65011757) join_2_0 join_2_1

theorem total : (twinPrimeSegment 62914605 65011757).card = 8602 := join_3_0

end S030All
end Sude.GeneratedTwinScan
