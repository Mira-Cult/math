import Sude.GeneratedTwinScan.S102C00
import Sude.GeneratedTwinScan.S102C01
import Sude.GeneratedTwinScan.S102C02
import Sude.GeneratedTwinScan.S102C03
import Sude.GeneratedTwinScan.S102C04
import Sude.GeneratedTwinScan.S102C05
import Sude.GeneratedTwinScan.S102C06
import Sude.GeneratedTwinScan.S102C07
import Sude.GeneratedTwinScan.S102C08
import Sude.GeneratedTwinScan.S102C09
import Sude.GeneratedTwinScan.S102C10
import Sude.GeneratedTwinScan.S102C11
import Sude.GeneratedTwinScan.S102C12
import Sude.GeneratedTwinScan.S102C13
import Sude.GeneratedTwinScan.S102C14
import Sude.GeneratedTwinScan.S102C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S102All

theorem join_0_0 : (twinPrimeSegment 213909549 214171693).card = 962 := by
  simpa using combineTwinPrimeSegments (by decide : 213909549 ≤ 214040621)
    (by decide : 214040621 ≤ 214171693) S102C00.total S102C01.total

theorem join_0_1 : (twinPrimeSegment 214171693 214433837).card = 931 := by
  simpa using combineTwinPrimeSegments (by decide : 214171693 ≤ 214302765)
    (by decide : 214302765 ≤ 214433837) S102C02.total S102C03.total

theorem join_0_2 : (twinPrimeSegment 214433837 214695981).card = 968 := by
  simpa using combineTwinPrimeSegments (by decide : 214433837 ≤ 214564909)
    (by decide : 214564909 ≤ 214695981) S102C04.total S102C05.total

theorem join_0_3 : (twinPrimeSegment 214695981 214958125).card = 943 := by
  simpa using combineTwinPrimeSegments (by decide : 214695981 ≤ 214827053)
    (by decide : 214827053 ≤ 214958125) S102C06.total S102C07.total

theorem join_0_4 : (twinPrimeSegment 214958125 215220269).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 214958125 ≤ 215089197)
    (by decide : 215089197 ≤ 215220269) S102C08.total S102C09.total

theorem join_0_5 : (twinPrimeSegment 215220269 215482413).card = 962 := by
  simpa using combineTwinPrimeSegments (by decide : 215220269 ≤ 215351341)
    (by decide : 215351341 ≤ 215482413) S102C10.total S102C11.total

theorem join_0_6 : (twinPrimeSegment 215482413 215744557).card = 948 := by
  simpa using combineTwinPrimeSegments (by decide : 215482413 ≤ 215613485)
    (by decide : 215613485 ≤ 215744557) S102C12.total S102C13.total

theorem join_0_7 : (twinPrimeSegment 215744557 216006701).card = 926 := by
  simpa using combineTwinPrimeSegments (by decide : 215744557 ≤ 215875629)
    (by decide : 215875629 ≤ 216006701) S102C14.total S102C15.total

theorem join_1_0 : (twinPrimeSegment 213909549 214433837).card = 1893 := by
  simpa using combineTwinPrimeSegments (by decide : 213909549 ≤ 214171693)
    (by decide : 214171693 ≤ 214433837) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 214433837 214958125).card = 1911 := by
  simpa using combineTwinPrimeSegments (by decide : 214433837 ≤ 214695981)
    (by decide : 214695981 ≤ 214958125) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 214958125 215482413).card = 1864 := by
  simpa using combineTwinPrimeSegments (by decide : 214958125 ≤ 215220269)
    (by decide : 215220269 ≤ 215482413) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 215482413 216006701).card = 1874 := by
  simpa using combineTwinPrimeSegments (by decide : 215482413 ≤ 215744557)
    (by decide : 215744557 ≤ 216006701) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 213909549 214958125).card = 3804 := by
  simpa using combineTwinPrimeSegments (by decide : 213909549 ≤ 214433837)
    (by decide : 214433837 ≤ 214958125) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 214958125 216006701).card = 3738 := by
  simpa using combineTwinPrimeSegments (by decide : 214958125 ≤ 215482413)
    (by decide : 215482413 ≤ 216006701) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 213909549 216006701).card = 7542 := by
  simpa using combineTwinPrimeSegments (by decide : 213909549 ≤ 214958125)
    (by decide : 214958125 ≤ 216006701) join_2_0 join_2_1

theorem total : (twinPrimeSegment 213909549 216006701).card = 7542 := join_3_0

end S102All
end Sude.GeneratedTwinScan
