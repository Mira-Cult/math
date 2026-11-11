import Sude.GeneratedTwinScan.S133C00
import Sude.GeneratedTwinScan.S133C01
import Sude.GeneratedTwinScan.S133C02
import Sude.GeneratedTwinScan.S133C03
import Sude.GeneratedTwinScan.S133C04
import Sude.GeneratedTwinScan.S133C05
import Sude.GeneratedTwinScan.S133C06
import Sude.GeneratedTwinScan.S133C07
import Sude.GeneratedTwinScan.S133C08
import Sude.GeneratedTwinScan.S133C09
import Sude.GeneratedTwinScan.S133C10
import Sude.GeneratedTwinScan.S133C11
import Sude.GeneratedTwinScan.S133C12
import Sude.GeneratedTwinScan.S133C13
import Sude.GeneratedTwinScan.S133C14
import Sude.GeneratedTwinScan.S133C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S133All

theorem join_0_0 : (twinPrimeSegment 278921261 279183405).card = 935 := by
  simpa using combineTwinPrimeSegments (by decide : 278921261 ≤ 279052333)
    (by decide : 279052333 ≤ 279183405) S133C00.total S133C01.total

theorem join_0_1 : (twinPrimeSegment 279183405 279445549).card = 941 := by
  simpa using combineTwinPrimeSegments (by decide : 279183405 ≤ 279314477)
    (by decide : 279314477 ≤ 279445549) S133C02.total S133C03.total

theorem join_0_2 : (twinPrimeSegment 279445549 279707693).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 279445549 ≤ 279576621)
    (by decide : 279576621 ≤ 279707693) S133C04.total S133C05.total

theorem join_0_3 : (twinPrimeSegment 279707693 279969837).card = 948 := by
  simpa using combineTwinPrimeSegments (by decide : 279707693 ≤ 279838765)
    (by decide : 279838765 ≤ 279969837) S133C06.total S133C07.total

theorem join_0_4 : (twinPrimeSegment 279969837 280231981).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 279969837 ≤ 280100909)
    (by decide : 280100909 ≤ 280231981) S133C08.total S133C09.total

theorem join_0_5 : (twinPrimeSegment 280231981 280494125).card = 932 := by
  simpa using combineTwinPrimeSegments (by decide : 280231981 ≤ 280363053)
    (by decide : 280363053 ≤ 280494125) S133C10.total S133C11.total

theorem join_0_6 : (twinPrimeSegment 280494125 280756269).card = 949 := by
  simpa using combineTwinPrimeSegments (by decide : 280494125 ≤ 280625197)
    (by decide : 280625197 ≤ 280756269) S133C12.total S133C13.total

theorem join_0_7 : (twinPrimeSegment 280756269 281018413).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 280756269 ≤ 280887341)
    (by decide : 280887341 ≤ 281018413) S133C14.total S133C15.total

theorem join_1_0 : (twinPrimeSegment 278921261 279445549).card = 1876 := by
  simpa using combineTwinPrimeSegments (by decide : 278921261 ≤ 279183405)
    (by decide : 279183405 ≤ 279445549) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 279445549 279969837).card = 1846 := by
  simpa using combineTwinPrimeSegments (by decide : 279445549 ≤ 279707693)
    (by decide : 279707693 ≤ 279969837) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 279969837 280494125).card = 1837 := by
  simpa using combineTwinPrimeSegments (by decide : 279969837 ≤ 280231981)
    (by decide : 280231981 ≤ 280494125) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 280494125 281018413).card = 1872 := by
  simpa using combineTwinPrimeSegments (by decide : 280494125 ≤ 280756269)
    (by decide : 280756269 ≤ 281018413) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 278921261 279969837).card = 3722 := by
  simpa using combineTwinPrimeSegments (by decide : 278921261 ≤ 279445549)
    (by decide : 279445549 ≤ 279969837) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 279969837 281018413).card = 3709 := by
  simpa using combineTwinPrimeSegments (by decide : 279969837 ≤ 280494125)
    (by decide : 280494125 ≤ 281018413) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 278921261 281018413).card = 7431 := by
  simpa using combineTwinPrimeSegments (by decide : 278921261 ≤ 279969837)
    (by decide : 279969837 ≤ 281018413) join_2_0 join_2_1

theorem total : (twinPrimeSegment 278921261 281018413).card = 7431 := join_3_0

end S133All
end Sude.GeneratedTwinScan
