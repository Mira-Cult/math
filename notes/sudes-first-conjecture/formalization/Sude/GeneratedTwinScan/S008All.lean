import Sude.GeneratedTwinScan.S008C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S008All

theorem join_0_0 : (twinPrimeSegment 16777261 17039405).card = 1245 := by
  simpa using combineTwinPrimeSegments (by decide : 16777261 ≤ 16908333)
    (by decide : 16908333 ≤ 17039405) S008C00.total S008C01.total

theorem join_0_1 : (twinPrimeSegment 17039405 17301549).card = 1258 := by
  simpa using combineTwinPrimeSegments (by decide : 17039405 ≤ 17170477)
    (by decide : 17170477 ≤ 17301549) S008C02.total S008C03.total

theorem join_0_2 : (twinPrimeSegment 17301549 17563693).card = 1254 := by
  simpa using combineTwinPrimeSegments (by decide : 17301549 ≤ 17432621)
    (by decide : 17432621 ≤ 17563693) S008C04.total S008C05.total

theorem join_0_3 : (twinPrimeSegment 17563693 17825837).card = 1269 := by
  simpa using combineTwinPrimeSegments (by decide : 17563693 ≤ 17694765)
    (by decide : 17694765 ≤ 17825837) S008C06.total S008C07.total

theorem join_0_4 : (twinPrimeSegment 17825837 18087981).card = 1226 := by
  simpa using combineTwinPrimeSegments (by decide : 17825837 ≤ 17956909)
    (by decide : 17956909 ≤ 18087981) S008C08.total S008C09.total

theorem join_0_5 : (twinPrimeSegment 18087981 18350125).card = 1226 := by
  simpa using combineTwinPrimeSegments (by decide : 18087981 ≤ 18219053)
    (by decide : 18219053 ≤ 18350125) S008C10.total S008C11.total

theorem join_0_6 : (twinPrimeSegment 18350125 18612269).card = 1224 := by
  simpa using combineTwinPrimeSegments (by decide : 18350125 ≤ 18481197)
    (by decide : 18481197 ≤ 18612269) S008C12.total S008C13.total

theorem join_0_7 : (twinPrimeSegment 18612269 18874413).card = 1272 := by
  simpa using combineTwinPrimeSegments (by decide : 18612269 ≤ 18743341)
    (by decide : 18743341 ≤ 18874413) S008C14.total S008C15.total

theorem join_1_0 : (twinPrimeSegment 16777261 17301549).card = 2503 := by
  simpa using combineTwinPrimeSegments (by decide : 16777261 ≤ 17039405)
    (by decide : 17039405 ≤ 17301549) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 17301549 17825837).card = 2523 := by
  simpa using combineTwinPrimeSegments (by decide : 17301549 ≤ 17563693)
    (by decide : 17563693 ≤ 17825837) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 17825837 18350125).card = 2452 := by
  simpa using combineTwinPrimeSegments (by decide : 17825837 ≤ 18087981)
    (by decide : 18087981 ≤ 18350125) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 18350125 18874413).card = 2496 := by
  simpa using combineTwinPrimeSegments (by decide : 18350125 ≤ 18612269)
    (by decide : 18612269 ≤ 18874413) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 16777261 17825837).card = 5026 := by
  simpa using combineTwinPrimeSegments (by decide : 16777261 ≤ 17301549)
    (by decide : 17301549 ≤ 17825837) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 17825837 18874413).card = 4948 := by
  simpa using combineTwinPrimeSegments (by decide : 17825837 ≤ 18350125)
    (by decide : 18350125 ≤ 18874413) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 16777261 18874413).card = 9974 := by
  simpa using combineTwinPrimeSegments (by decide : 16777261 ≤ 17825837)
    (by decide : 17825837 ≤ 18874413) join_2_0 join_2_1

theorem total : (twinPrimeSegment 16777261 18874413).card = 9974 := join_3_0

end S008All
end Sude.GeneratedTwinScan
