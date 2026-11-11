import Sude.GeneratedTwinScan.S065C00
import Sude.GeneratedTwinScan.S065C01
import Sude.GeneratedTwinScan.S065C02
import Sude.GeneratedTwinScan.S065C03
import Sude.GeneratedTwinScan.S065C04
import Sude.GeneratedTwinScan.S065C05
import Sude.GeneratedTwinScan.S065C06
import Sude.GeneratedTwinScan.S065C07
import Sude.GeneratedTwinScan.S065C08
import Sude.GeneratedTwinScan.S065C09
import Sude.GeneratedTwinScan.S065C10
import Sude.GeneratedTwinScan.S065C11
import Sude.GeneratedTwinScan.S065C12
import Sude.GeneratedTwinScan.S065C13
import Sude.GeneratedTwinScan.S065C14
import Sude.GeneratedTwinScan.S065C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S065All

theorem join_0_0 : (twinPrimeSegment 136314925 136577069).card = 1040 := by
  simpa using combineTwinPrimeSegments (by decide : 136314925 ≤ 136445997)
    (by decide : 136445997 ≤ 136577069) S065C00.total S065C01.total

theorem join_0_1 : (twinPrimeSegment 136577069 136839213).card = 993 := by
  simpa using combineTwinPrimeSegments (by decide : 136577069 ≤ 136708141)
    (by decide : 136708141 ≤ 136839213) S065C02.total S065C03.total

theorem join_0_2 : (twinPrimeSegment 136839213 137101357).card = 928 := by
  simpa using combineTwinPrimeSegments (by decide : 136839213 ≤ 136970285)
    (by decide : 136970285 ≤ 137101357) S065C04.total S065C05.total

theorem join_0_3 : (twinPrimeSegment 137101357 137363501).card = 986 := by
  simpa using combineTwinPrimeSegments (by decide : 137101357 ≤ 137232429)
    (by decide : 137232429 ≤ 137363501) S065C06.total S065C07.total

theorem join_0_4 : (twinPrimeSegment 137363501 137625645).card = 1037 := by
  simpa using combineTwinPrimeSegments (by decide : 137363501 ≤ 137494573)
    (by decide : 137494573 ≤ 137625645) S065C08.total S065C09.total

theorem join_0_5 : (twinPrimeSegment 137625645 137887789).card = 985 := by
  simpa using combineTwinPrimeSegments (by decide : 137625645 ≤ 137756717)
    (by decide : 137756717 ≤ 137887789) S065C10.total S065C11.total

theorem join_0_6 : (twinPrimeSegment 137887789 138149933).card = 969 := by
  simpa using combineTwinPrimeSegments (by decide : 137887789 ≤ 138018861)
    (by decide : 138018861 ≤ 138149933) S065C12.total S065C13.total

theorem join_0_7 : (twinPrimeSegment 138149933 138412077).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 138149933 ≤ 138281005)
    (by decide : 138281005 ≤ 138412077) S065C14.total S065C15.total

theorem join_1_0 : (twinPrimeSegment 136314925 136839213).card = 2033 := by
  simpa using combineTwinPrimeSegments (by decide : 136314925 ≤ 136577069)
    (by decide : 136577069 ≤ 136839213) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 136839213 137363501).card = 1914 := by
  simpa using combineTwinPrimeSegments (by decide : 136839213 ≤ 137101357)
    (by decide : 137101357 ≤ 137363501) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 137363501 137887789).card = 2022 := by
  simpa using combineTwinPrimeSegments (by decide : 137363501 ≤ 137625645)
    (by decide : 137625645 ≤ 137887789) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 137887789 138412077).card = 1951 := by
  simpa using combineTwinPrimeSegments (by decide : 137887789 ≤ 138149933)
    (by decide : 138149933 ≤ 138412077) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 136314925 137363501).card = 3947 := by
  simpa using combineTwinPrimeSegments (by decide : 136314925 ≤ 136839213)
    (by decide : 136839213 ≤ 137363501) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 137363501 138412077).card = 3973 := by
  simpa using combineTwinPrimeSegments (by decide : 137363501 ≤ 137887789)
    (by decide : 137887789 ≤ 138412077) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 136314925 138412077).card = 7920 := by
  simpa using combineTwinPrimeSegments (by decide : 136314925 ≤ 137363501)
    (by decide : 137363501 ≤ 138412077) join_2_0 join_2_1

theorem total : (twinPrimeSegment 136314925 138412077).card = 7920 := join_3_0

end S065All
end Sude.GeneratedTwinScan
