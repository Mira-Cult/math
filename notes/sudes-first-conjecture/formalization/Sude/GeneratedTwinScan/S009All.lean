import Sude.GeneratedTwinScan.S009C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S009All

theorem join_0_0 : (twinPrimeSegment 18874413 19136557).card = 1258 := by
  simpa using combineTwinPrimeSegments (by decide : 18874413 ≤ 19005485)
    (by decide : 19005485 ≤ 19136557) S009C00.total S009C01.total

theorem join_0_1 : (twinPrimeSegment 19136557 19398701).card = 1205 := by
  simpa using combineTwinPrimeSegments (by decide : 19136557 ≤ 19267629)
    (by decide : 19267629 ≤ 19398701) S009C02.total S009C03.total

theorem join_0_2 : (twinPrimeSegment 19398701 19660845).card = 1200 := by
  simpa using combineTwinPrimeSegments (by decide : 19398701 ≤ 19529773)
    (by decide : 19529773 ≤ 19660845) S009C04.total S009C05.total

theorem join_0_3 : (twinPrimeSegment 19660845 19922989).card = 1175 := by
  simpa using combineTwinPrimeSegments (by decide : 19660845 ≤ 19791917)
    (by decide : 19791917 ≤ 19922989) S009C06.total S009C07.total

theorem join_0_4 : (twinPrimeSegment 19922989 20185133).card = 1245 := by
  simpa using combineTwinPrimeSegments (by decide : 19922989 ≤ 20054061)
    (by decide : 20054061 ≤ 20185133) S009C08.total S009C09.total

theorem join_0_5 : (twinPrimeSegment 20185133 20447277).card = 1220 := by
  simpa using combineTwinPrimeSegments (by decide : 20185133 ≤ 20316205)
    (by decide : 20316205 ≤ 20447277) S009C10.total S009C11.total

theorem join_0_6 : (twinPrimeSegment 20447277 20709421).card = 1207 := by
  simpa using combineTwinPrimeSegments (by decide : 20447277 ≤ 20578349)
    (by decide : 20578349 ≤ 20709421) S009C12.total S009C13.total

theorem join_0_7 : (twinPrimeSegment 20709421 20971565).card = 1236 := by
  simpa using combineTwinPrimeSegments (by decide : 20709421 ≤ 20840493)
    (by decide : 20840493 ≤ 20971565) S009C14.total S009C15.total

theorem join_1_0 : (twinPrimeSegment 18874413 19398701).card = 2463 := by
  simpa using combineTwinPrimeSegments (by decide : 18874413 ≤ 19136557)
    (by decide : 19136557 ≤ 19398701) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 19398701 19922989).card = 2375 := by
  simpa using combineTwinPrimeSegments (by decide : 19398701 ≤ 19660845)
    (by decide : 19660845 ≤ 19922989) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 19922989 20447277).card = 2465 := by
  simpa using combineTwinPrimeSegments (by decide : 19922989 ≤ 20185133)
    (by decide : 20185133 ≤ 20447277) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 20447277 20971565).card = 2443 := by
  simpa using combineTwinPrimeSegments (by decide : 20447277 ≤ 20709421)
    (by decide : 20709421 ≤ 20971565) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 18874413 19922989).card = 4838 := by
  simpa using combineTwinPrimeSegments (by decide : 18874413 ≤ 19398701)
    (by decide : 19398701 ≤ 19922989) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 19922989 20971565).card = 4908 := by
  simpa using combineTwinPrimeSegments (by decide : 19922989 ≤ 20447277)
    (by decide : 20447277 ≤ 20971565) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 18874413 20971565).card = 9746 := by
  simpa using combineTwinPrimeSegments (by decide : 18874413 ≤ 19922989)
    (by decide : 19922989 ≤ 20971565) join_2_0 join_2_1

theorem total : (twinPrimeSegment 18874413 20971565).card = 9746 := join_3_0

end S009All
end Sude.GeneratedTwinScan
