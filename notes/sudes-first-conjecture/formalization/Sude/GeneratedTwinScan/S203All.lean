import Sude.GeneratedTwinScan.S203C00
import Sude.GeneratedTwinScan.S203C01
import Sude.GeneratedTwinScan.S203C02
import Sude.GeneratedTwinScan.S203C03
import Sude.GeneratedTwinScan.S203C04
import Sude.GeneratedTwinScan.S203C05
import Sude.GeneratedTwinScan.S203C06
import Sude.GeneratedTwinScan.S203C07
import Sude.GeneratedTwinScan.S203C08
import Sude.GeneratedTwinScan.S203C09
import Sude.GeneratedTwinScan.S203C10
import Sude.GeneratedTwinScan.S203C11
import Sude.GeneratedTwinScan.S203C12
import Sude.GeneratedTwinScan.S203C13
import Sude.GeneratedTwinScan.S203C14
import Sude.GeneratedTwinScan.S203C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S203All

theorem join_0_0 : (twinPrimeSegment 425721901 425984045).card = 884 := by
  simpa using combineTwinPrimeSegments (by decide : 425721901 ≤ 425852973)
    (by decide : 425852973 ≤ 425984045) S203C00.total S203C01.total

theorem join_0_1 : (twinPrimeSegment 425984045 426246189).card = 886 := by
  simpa using combineTwinPrimeSegments (by decide : 425984045 ≤ 426115117)
    (by decide : 426115117 ≤ 426246189) S203C02.total S203C03.total

theorem join_0_2 : (twinPrimeSegment 426246189 426508333).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 426246189 ≤ 426377261)
    (by decide : 426377261 ≤ 426508333) S203C04.total S203C05.total

theorem join_0_3 : (twinPrimeSegment 426508333 426770477).card = 892 := by
  simpa using combineTwinPrimeSegments (by decide : 426508333 ≤ 426639405)
    (by decide : 426639405 ≤ 426770477) S203C06.total S203C07.total

theorem join_0_4 : (twinPrimeSegment 426770477 427032621).card = 800 := by
  simpa using combineTwinPrimeSegments (by decide : 426770477 ≤ 426901549)
    (by decide : 426901549 ≤ 427032621) S203C08.total S203C09.total

theorem join_0_5 : (twinPrimeSegment 427032621 427294765).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 427032621 ≤ 427163693)
    (by decide : 427163693 ≤ 427294765) S203C10.total S203C11.total

theorem join_0_6 : (twinPrimeSegment 427294765 427556909).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 427294765 ≤ 427425837)
    (by decide : 427425837 ≤ 427556909) S203C12.total S203C13.total

theorem join_0_7 : (twinPrimeSegment 427556909 427819053).card = 858 := by
  simpa using combineTwinPrimeSegments (by decide : 427556909 ≤ 427687981)
    (by decide : 427687981 ≤ 427819053) S203C14.total S203C15.total

theorem join_1_0 : (twinPrimeSegment 425721901 426246189).card = 1770 := by
  simpa using combineTwinPrimeSegments (by decide : 425721901 ≤ 425984045)
    (by decide : 425984045 ≤ 426246189) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 426246189 426770477).card = 1800 := by
  simpa using combineTwinPrimeSegments (by decide : 426246189 ≤ 426508333)
    (by decide : 426508333 ≤ 426770477) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 426770477 427294765).card = 1666 := by
  simpa using combineTwinPrimeSegments (by decide : 426770477 ≤ 427032621)
    (by decide : 427032621 ≤ 427294765) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 427294765 427819053).card = 1732 := by
  simpa using combineTwinPrimeSegments (by decide : 427294765 ≤ 427556909)
    (by decide : 427556909 ≤ 427819053) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 425721901 426770477).card = 3570 := by
  simpa using combineTwinPrimeSegments (by decide : 425721901 ≤ 426246189)
    (by decide : 426246189 ≤ 426770477) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 426770477 427819053).card = 3398 := by
  simpa using combineTwinPrimeSegments (by decide : 426770477 ≤ 427294765)
    (by decide : 427294765 ≤ 427819053) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 425721901 427819053).card = 6968 := by
  simpa using combineTwinPrimeSegments (by decide : 425721901 ≤ 426770477)
    (by decide : 426770477 ≤ 427819053) join_2_0 join_2_1

theorem total : (twinPrimeSegment 425721901 427819053).card = 6968 := join_3_0

end S203All
end Sude.GeneratedTwinScan
