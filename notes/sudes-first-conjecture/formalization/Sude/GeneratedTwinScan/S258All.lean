import Sude.GeneratedTwinScan.S258C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S258All

theorem join_0_0 : (twinPrimeSegment 541065261 541327405).card = 817 := by
  simpa using combineTwinPrimeSegments (by decide : 541065261 ≤ 541196333)
    (by decide : 541196333 ≤ 541327405) S258C00.total S258C01.total

theorem join_0_1 : (twinPrimeSegment 541327405 541589549).card = 882 := by
  simpa using combineTwinPrimeSegments (by decide : 541327405 ≤ 541458477)
    (by decide : 541458477 ≤ 541589549) S258C02.total S258C03.total

theorem join_0_2 : (twinPrimeSegment 541589549 541851693).card = 840 := by
  simpa using combineTwinPrimeSegments (by decide : 541589549 ≤ 541720621)
    (by decide : 541720621 ≤ 541851693) S258C04.total S258C05.total

theorem join_0_3 : (twinPrimeSegment 541851693 542113837).card = 830 := by
  simpa using combineTwinPrimeSegments (by decide : 541851693 ≤ 541982765)
    (by decide : 541982765 ≤ 542113837) S258C06.total S258C07.total

theorem join_0_4 : (twinPrimeSegment 542113837 542375981).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 542113837 ≤ 542244909)
    (by decide : 542244909 ≤ 542375981) S258C08.total S258C09.total

theorem join_0_5 : (twinPrimeSegment 542375981 542638125).card = 818 := by
  simpa using combineTwinPrimeSegments (by decide : 542375981 ≤ 542507053)
    (by decide : 542507053 ≤ 542638125) S258C10.total S258C11.total

theorem join_0_6 : (twinPrimeSegment 542638125 542900269).card = 850 := by
  simpa using combineTwinPrimeSegments (by decide : 542638125 ≤ 542769197)
    (by decide : 542769197 ≤ 542900269) S258C12.total S258C13.total

theorem join_0_7 : (twinPrimeSegment 542900269 543162413).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 542900269 ≤ 543031341)
    (by decide : 543031341 ≤ 543162413) S258C14.total S258C15.total

theorem join_1_0 : (twinPrimeSegment 541065261 541589549).card = 1699 := by
  simpa using combineTwinPrimeSegments (by decide : 541065261 ≤ 541327405)
    (by decide : 541327405 ≤ 541589549) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 541589549 542113837).card = 1670 := by
  simpa using combineTwinPrimeSegments (by decide : 541589549 ≤ 541851693)
    (by decide : 541851693 ≤ 542113837) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 542113837 542638125).card = 1682 := by
  simpa using combineTwinPrimeSegments (by decide : 542113837 ≤ 542375981)
    (by decide : 542375981 ≤ 542638125) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 542638125 543162413).card = 1711 := by
  simpa using combineTwinPrimeSegments (by decide : 542638125 ≤ 542900269)
    (by decide : 542900269 ≤ 543162413) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 541065261 542113837).card = 3369 := by
  simpa using combineTwinPrimeSegments (by decide : 541065261 ≤ 541589549)
    (by decide : 541589549 ≤ 542113837) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 542113837 543162413).card = 3393 := by
  simpa using combineTwinPrimeSegments (by decide : 542113837 ≤ 542638125)
    (by decide : 542638125 ≤ 543162413) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 541065261 543162413).card = 6762 := by
  simpa using combineTwinPrimeSegments (by decide : 541065261 ≤ 542113837)
    (by decide : 542113837 ≤ 543162413) join_2_0 join_2_1

theorem total : (twinPrimeSegment 541065261 543162413).card = 6762 := join_3_0

end S258All
end Sude.GeneratedTwinScan
