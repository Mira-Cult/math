import Sude.GeneratedTwinScan.S026C00
import Sude.GeneratedTwinScan.S026C01
import Sude.GeneratedTwinScan.S026C02
import Sude.GeneratedTwinScan.S026C03
import Sude.GeneratedTwinScan.S026C04
import Sude.GeneratedTwinScan.S026C05
import Sude.GeneratedTwinScan.S026C06
import Sude.GeneratedTwinScan.S026C07
import Sude.GeneratedTwinScan.S026C08
import Sude.GeneratedTwinScan.S026C09
import Sude.GeneratedTwinScan.S026C10
import Sude.GeneratedTwinScan.S026C11
import Sude.GeneratedTwinScan.S026C12
import Sude.GeneratedTwinScan.S026C13
import Sude.GeneratedTwinScan.S026C14
import Sude.GeneratedTwinScan.S026C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S026All

theorem join_0_0 : (twinPrimeSegment 54525997 54788141).card = 1114 := by
  simpa using combineTwinPrimeSegments (by decide : 54525997 ≤ 54657069)
    (by decide : 54657069 ≤ 54788141) S026C00.total S026C01.total

theorem join_0_1 : (twinPrimeSegment 54788141 55050285).card = 1097 := by
  simpa using combineTwinPrimeSegments (by decide : 54788141 ≤ 54919213)
    (by decide : 54919213 ≤ 55050285) S026C02.total S026C03.total

theorem join_0_2 : (twinPrimeSegment 55050285 55312429).card = 1023 := by
  simpa using combineTwinPrimeSegments (by decide : 55050285 ≤ 55181357)
    (by decide : 55181357 ≤ 55312429) S026C04.total S026C05.total

theorem join_0_3 : (twinPrimeSegment 55312429 55574573).card = 1100 := by
  simpa using combineTwinPrimeSegments (by decide : 55312429 ≤ 55443501)
    (by decide : 55443501 ≤ 55574573) S026C06.total S026C07.total

theorem join_0_4 : (twinPrimeSegment 55574573 55836717).card = 1125 := by
  simpa using combineTwinPrimeSegments (by decide : 55574573 ≤ 55705645)
    (by decide : 55705645 ≤ 55836717) S026C08.total S026C09.total

theorem join_0_5 : (twinPrimeSegment 55836717 56098861).card = 1085 := by
  simpa using combineTwinPrimeSegments (by decide : 55836717 ≤ 55967789)
    (by decide : 55967789 ≤ 56098861) S026C10.total S026C11.total

theorem join_0_6 : (twinPrimeSegment 56098861 56361005).card = 1144 := by
  simpa using combineTwinPrimeSegments (by decide : 56098861 ≤ 56229933)
    (by decide : 56229933 ≤ 56361005) S026C12.total S026C13.total

theorem join_0_7 : (twinPrimeSegment 56361005 56623149).card = 1052 := by
  simpa using combineTwinPrimeSegments (by decide : 56361005 ≤ 56492077)
    (by decide : 56492077 ≤ 56623149) S026C14.total S026C15.total

theorem join_1_0 : (twinPrimeSegment 54525997 55050285).card = 2211 := by
  simpa using combineTwinPrimeSegments (by decide : 54525997 ≤ 54788141)
    (by decide : 54788141 ≤ 55050285) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 55050285 55574573).card = 2123 := by
  simpa using combineTwinPrimeSegments (by decide : 55050285 ≤ 55312429)
    (by decide : 55312429 ≤ 55574573) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 55574573 56098861).card = 2210 := by
  simpa using combineTwinPrimeSegments (by decide : 55574573 ≤ 55836717)
    (by decide : 55836717 ≤ 56098861) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 56098861 56623149).card = 2196 := by
  simpa using combineTwinPrimeSegments (by decide : 56098861 ≤ 56361005)
    (by decide : 56361005 ≤ 56623149) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 54525997 55574573).card = 4334 := by
  simpa using combineTwinPrimeSegments (by decide : 54525997 ≤ 55050285)
    (by decide : 55050285 ≤ 55574573) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 55574573 56623149).card = 4406 := by
  simpa using combineTwinPrimeSegments (by decide : 55574573 ≤ 56098861)
    (by decide : 56098861 ≤ 56623149) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 54525997 56623149).card = 8740 := by
  simpa using combineTwinPrimeSegments (by decide : 54525997 ≤ 55574573)
    (by decide : 55574573 ≤ 56623149) join_2_0 join_2_1

theorem total : (twinPrimeSegment 54525997 56623149).card = 8740 := join_3_0

end S026All
end Sude.GeneratedTwinScan
