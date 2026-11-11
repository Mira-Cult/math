import Sude.GeneratedTwinScan.S003C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S003All

theorem join_0_0 : (twinPrimeSegment 6291501 6553645).card = 1374 := by
  simpa using combineTwinPrimeSegments (by decide : 6291501 ≤ 6422573)
    (by decide : 6422573 ≤ 6553645) S003C00.total S003C01.total

theorem join_0_1 : (twinPrimeSegment 6553645 6815789).card = 1356 := by
  simpa using combineTwinPrimeSegments (by decide : 6553645 ≤ 6684717)
    (by decide : 6684717 ≤ 6815789) S003C02.total S003C03.total

theorem join_0_2 : (twinPrimeSegment 6815789 7077933).card = 1403 := by
  simpa using combineTwinPrimeSegments (by decide : 6815789 ≤ 6946861)
    (by decide : 6946861 ≤ 7077933) S003C04.total S003C05.total

theorem join_0_3 : (twinPrimeSegment 7077933 7340077).card = 1393 := by
  simpa using combineTwinPrimeSegments (by decide : 7077933 ≤ 7209005)
    (by decide : 7209005 ≤ 7340077) S003C06.total S003C07.total

theorem join_0_4 : (twinPrimeSegment 7340077 7602221).card = 1420 := by
  simpa using combineTwinPrimeSegments (by decide : 7340077 ≤ 7471149)
    (by decide : 7471149 ≤ 7602221) S003C08.total S003C09.total

theorem join_0_5 : (twinPrimeSegment 7602221 7864365).card = 1427 := by
  simpa using combineTwinPrimeSegments (by decide : 7602221 ≤ 7733293)
    (by decide : 7733293 ≤ 7864365) S003C10.total S003C11.total

theorem join_0_6 : (twinPrimeSegment 7864365 8126509).card = 1361 := by
  simpa using combineTwinPrimeSegments (by decide : 7864365 ≤ 7995437)
    (by decide : 7995437 ≤ 8126509) S003C12.total S003C13.total

theorem join_0_7 : (twinPrimeSegment 8126509 8388653).card = 1375 := by
  simpa using combineTwinPrimeSegments (by decide : 8126509 ≤ 8257581)
    (by decide : 8257581 ≤ 8388653) S003C14.total S003C15.total

theorem join_1_0 : (twinPrimeSegment 6291501 6815789).card = 2730 := by
  simpa using combineTwinPrimeSegments (by decide : 6291501 ≤ 6553645)
    (by decide : 6553645 ≤ 6815789) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 6815789 7340077).card = 2796 := by
  simpa using combineTwinPrimeSegments (by decide : 6815789 ≤ 7077933)
    (by decide : 7077933 ≤ 7340077) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 7340077 7864365).card = 2847 := by
  simpa using combineTwinPrimeSegments (by decide : 7340077 ≤ 7602221)
    (by decide : 7602221 ≤ 7864365) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 7864365 8388653).card = 2736 := by
  simpa using combineTwinPrimeSegments (by decide : 7864365 ≤ 8126509)
    (by decide : 8126509 ≤ 8388653) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 6291501 7340077).card = 5526 := by
  simpa using combineTwinPrimeSegments (by decide : 6291501 ≤ 6815789)
    (by decide : 6815789 ≤ 7340077) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 7340077 8388653).card = 5583 := by
  simpa using combineTwinPrimeSegments (by decide : 7340077 ≤ 7864365)
    (by decide : 7864365 ≤ 8388653) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 6291501 8388653).card = 11109 := by
  simpa using combineTwinPrimeSegments (by decide : 6291501 ≤ 7340077)
    (by decide : 7340077 ≤ 8388653) join_2_0 join_2_1

theorem total : (twinPrimeSegment 6291501 8388653).card = 11109 := join_3_0

end S003All
end Sude.GeneratedTwinScan
