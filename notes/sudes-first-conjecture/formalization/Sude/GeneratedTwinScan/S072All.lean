import Sude.GeneratedTwinScan.S072C00
import Sude.GeneratedTwinScan.S072C01
import Sude.GeneratedTwinScan.S072C02
import Sude.GeneratedTwinScan.S072C03
import Sude.GeneratedTwinScan.S072C04
import Sude.GeneratedTwinScan.S072C05
import Sude.GeneratedTwinScan.S072C06
import Sude.GeneratedTwinScan.S072C07
import Sude.GeneratedTwinScan.S072C08
import Sude.GeneratedTwinScan.S072C09
import Sude.GeneratedTwinScan.S072C10
import Sude.GeneratedTwinScan.S072C11
import Sude.GeneratedTwinScan.S072C12
import Sude.GeneratedTwinScan.S072C13
import Sude.GeneratedTwinScan.S072C14
import Sude.GeneratedTwinScan.S072C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S072All

theorem join_0_0 : (twinPrimeSegment 150994989 151257133).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 150994989 ≤ 151126061)
    (by decide : 151126061 ≤ 151257133) S072C00.total S072C01.total

theorem join_0_1 : (twinPrimeSegment 151257133 151519277).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 151257133 ≤ 151388205)
    (by decide : 151388205 ≤ 151519277) S072C02.total S072C03.total

theorem join_0_2 : (twinPrimeSegment 151519277 151781421).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 151519277 ≤ 151650349)
    (by decide : 151650349 ≤ 151781421) S072C04.total S072C05.total

theorem join_0_3 : (twinPrimeSegment 151781421 152043565).card = 971 := by
  simpa using combineTwinPrimeSegments (by decide : 151781421 ≤ 151912493)
    (by decide : 151912493 ≤ 152043565) S072C06.total S072C07.total

theorem join_0_4 : (twinPrimeSegment 152043565 152305709).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 152043565 ≤ 152174637)
    (by decide : 152174637 ≤ 152305709) S072C08.total S072C09.total

theorem join_0_5 : (twinPrimeSegment 152305709 152567853).card = 952 := by
  simpa using combineTwinPrimeSegments (by decide : 152305709 ≤ 152436781)
    (by decide : 152436781 ≤ 152567853) S072C10.total S072C11.total

theorem join_0_6 : (twinPrimeSegment 152567853 152829997).card = 983 := by
  simpa using combineTwinPrimeSegments (by decide : 152567853 ≤ 152698925)
    (by decide : 152698925 ≤ 152829997) S072C12.total S072C13.total

theorem join_0_7 : (twinPrimeSegment 152829997 153092141).card = 966 := by
  simpa using combineTwinPrimeSegments (by decide : 152829997 ≤ 152961069)
    (by decide : 152961069 ≤ 153092141) S072C14.total S072C15.total

theorem join_1_0 : (twinPrimeSegment 150994989 151519277).card = 1939 := by
  simpa using combineTwinPrimeSegments (by decide : 150994989 ≤ 151257133)
    (by decide : 151257133 ≤ 151519277) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 151519277 152043565).card = 1935 := by
  simpa using combineTwinPrimeSegments (by decide : 151519277 ≤ 151781421)
    (by decide : 151781421 ≤ 152043565) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 152043565 152567853).card = 1886 := by
  simpa using combineTwinPrimeSegments (by decide : 152043565 ≤ 152305709)
    (by decide : 152305709 ≤ 152567853) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 152567853 153092141).card = 1949 := by
  simpa using combineTwinPrimeSegments (by decide : 152567853 ≤ 152829997)
    (by decide : 152829997 ≤ 153092141) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 150994989 152043565).card = 3874 := by
  simpa using combineTwinPrimeSegments (by decide : 150994989 ≤ 151519277)
    (by decide : 151519277 ≤ 152043565) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 152043565 153092141).card = 3835 := by
  simpa using combineTwinPrimeSegments (by decide : 152043565 ≤ 152567853)
    (by decide : 152567853 ≤ 153092141) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 150994989 153092141).card = 7709 := by
  simpa using combineTwinPrimeSegments (by decide : 150994989 ≤ 152043565)
    (by decide : 152043565 ≤ 153092141) join_2_0 join_2_1

theorem total : (twinPrimeSegment 150994989 153092141).card = 7709 := join_3_0

end S072All
end Sude.GeneratedTwinScan
