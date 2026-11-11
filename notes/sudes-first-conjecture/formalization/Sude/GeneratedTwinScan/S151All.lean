import Sude.GeneratedTwinScan.S151C00
import Sude.GeneratedTwinScan.S151C01
import Sude.GeneratedTwinScan.S151C02
import Sude.GeneratedTwinScan.S151C03
import Sude.GeneratedTwinScan.S151C04
import Sude.GeneratedTwinScan.S151C05
import Sude.GeneratedTwinScan.S151C06
import Sude.GeneratedTwinScan.S151C07
import Sude.GeneratedTwinScan.S151C08
import Sude.GeneratedTwinScan.S151C09
import Sude.GeneratedTwinScan.S151C10
import Sude.GeneratedTwinScan.S151C11
import Sude.GeneratedTwinScan.S151C12
import Sude.GeneratedTwinScan.S151C13
import Sude.GeneratedTwinScan.S151C14
import Sude.GeneratedTwinScan.S151C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S151All

theorem join_0_0 : (twinPrimeSegment 316669997 316932141).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 316669997 ≤ 316801069)
    (by decide : 316801069 ≤ 316932141) S151C00.total S151C01.total

theorem join_0_1 : (twinPrimeSegment 316932141 317194285).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 316932141 ≤ 317063213)
    (by decide : 317063213 ≤ 317194285) S151C02.total S151C03.total

theorem join_0_2 : (twinPrimeSegment 317194285 317456429).card = 944 := by
  simpa using combineTwinPrimeSegments (by decide : 317194285 ≤ 317325357)
    (by decide : 317325357 ≤ 317456429) S151C04.total S151C05.total

theorem join_0_3 : (twinPrimeSegment 317456429 317718573).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 317456429 ≤ 317587501)
    (by decide : 317587501 ≤ 317718573) S151C06.total S151C07.total

theorem join_0_4 : (twinPrimeSegment 317718573 317980717).card = 884 := by
  simpa using combineTwinPrimeSegments (by decide : 317718573 ≤ 317849645)
    (by decide : 317849645 ≤ 317980717) S151C08.total S151C09.total

theorem join_0_5 : (twinPrimeSegment 317980717 318242861).card = 937 := by
  simpa using combineTwinPrimeSegments (by decide : 317980717 ≤ 318111789)
    (by decide : 318111789 ≤ 318242861) S151C10.total S151C11.total

theorem join_0_6 : (twinPrimeSegment 318242861 318505005).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 318242861 ≤ 318373933)
    (by decide : 318373933 ≤ 318505005) S151C12.total S151C13.total

theorem join_0_7 : (twinPrimeSegment 318505005 318767149).card = 961 := by
  simpa using combineTwinPrimeSegments (by decide : 318505005 ≤ 318636077)
    (by decide : 318636077 ≤ 318767149) S151C14.total S151C15.total

theorem join_1_0 : (twinPrimeSegment 316669997 317194285).card = 1769 := by
  simpa using combineTwinPrimeSegments (by decide : 316669997 ≤ 316932141)
    (by decide : 316932141 ≤ 317194285) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 317194285 317718573).card = 1878 := by
  simpa using combineTwinPrimeSegments (by decide : 317194285 ≤ 317456429)
    (by decide : 317456429 ≤ 317718573) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 317718573 318242861).card = 1821 := by
  simpa using combineTwinPrimeSegments (by decide : 317718573 ≤ 317980717)
    (by decide : 317980717 ≤ 318242861) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 318242861 318767149).card = 1851 := by
  simpa using combineTwinPrimeSegments (by decide : 318242861 ≤ 318505005)
    (by decide : 318505005 ≤ 318767149) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 316669997 317718573).card = 3647 := by
  simpa using combineTwinPrimeSegments (by decide : 316669997 ≤ 317194285)
    (by decide : 317194285 ≤ 317718573) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 317718573 318767149).card = 3672 := by
  simpa using combineTwinPrimeSegments (by decide : 317718573 ≤ 318242861)
    (by decide : 318242861 ≤ 318767149) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 316669997 318767149).card = 7319 := by
  simpa using combineTwinPrimeSegments (by decide : 316669997 ≤ 317718573)
    (by decide : 317718573 ≤ 318767149) join_2_0 join_2_1

theorem total : (twinPrimeSegment 316669997 318767149).card = 7319 := join_3_0

end S151All
end Sude.GeneratedTwinScan
