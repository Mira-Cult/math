import Sude.GeneratedTwinScan.S257C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S257All

theorem join_0_0 : (twinPrimeSegment 538968109 539230253).card = 846 := by
  simpa using combineTwinPrimeSegments (by decide : 538968109 ≤ 539099181)
    (by decide : 539099181 ≤ 539230253) S257C00.total S257C01.total

theorem join_0_1 : (twinPrimeSegment 539230253 539492397).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 539230253 ≤ 539361325)
    (by decide : 539361325 ≤ 539492397) S257C02.total S257C03.total

theorem join_0_2 : (twinPrimeSegment 539492397 539754541).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 539492397 ≤ 539623469)
    (by decide : 539623469 ≤ 539754541) S257C04.total S257C05.total

theorem join_0_3 : (twinPrimeSegment 539754541 540016685).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 539754541 ≤ 539885613)
    (by decide : 539885613 ≤ 540016685) S257C06.total S257C07.total

theorem join_0_4 : (twinPrimeSegment 540016685 540278829).card = 843 := by
  simpa using combineTwinPrimeSegments (by decide : 540016685 ≤ 540147757)
    (by decide : 540147757 ≤ 540278829) S257C08.total S257C09.total

theorem join_0_5 : (twinPrimeSegment 540278829 540540973).card = 850 := by
  simpa using combineTwinPrimeSegments (by decide : 540278829 ≤ 540409901)
    (by decide : 540409901 ≤ 540540973) S257C10.total S257C11.total

theorem join_0_6 : (twinPrimeSegment 540540973 540803117).card = 841 := by
  simpa using combineTwinPrimeSegments (by decide : 540540973 ≤ 540672045)
    (by decide : 540672045 ≤ 540803117) S257C12.total S257C13.total

theorem join_0_7 : (twinPrimeSegment 540803117 541065261).card = 827 := by
  simpa using combineTwinPrimeSegments (by decide : 540803117 ≤ 540934189)
    (by decide : 540934189 ≤ 541065261) S257C14.total S257C15.total

theorem join_1_0 : (twinPrimeSegment 538968109 539492397).card = 1703 := by
  simpa using combineTwinPrimeSegments (by decide : 538968109 ≤ 539230253)
    (by decide : 539230253 ≤ 539492397) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 539492397 540016685).card = 1742 := by
  simpa using combineTwinPrimeSegments (by decide : 539492397 ≤ 539754541)
    (by decide : 539754541 ≤ 540016685) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 540016685 540540973).card = 1693 := by
  simpa using combineTwinPrimeSegments (by decide : 540016685 ≤ 540278829)
    (by decide : 540278829 ≤ 540540973) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 540540973 541065261).card = 1668 := by
  simpa using combineTwinPrimeSegments (by decide : 540540973 ≤ 540803117)
    (by decide : 540803117 ≤ 541065261) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 538968109 540016685).card = 3445 := by
  simpa using combineTwinPrimeSegments (by decide : 538968109 ≤ 539492397)
    (by decide : 539492397 ≤ 540016685) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 540016685 541065261).card = 3361 := by
  simpa using combineTwinPrimeSegments (by decide : 540016685 ≤ 540540973)
    (by decide : 540540973 ≤ 541065261) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 538968109 541065261).card = 6806 := by
  simpa using combineTwinPrimeSegments (by decide : 538968109 ≤ 540016685)
    (by decide : 540016685 ≤ 541065261) join_2_0 join_2_1

theorem total : (twinPrimeSegment 538968109 541065261).card = 6806 := join_3_0

end S257All
end Sude.GeneratedTwinScan
