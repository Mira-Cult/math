import Sude.GeneratedTwinScan.S002C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S002All

theorem join_0_0 : (twinPrimeSegment 4194349 4456493).card = 1466 := by
  simpa using combineTwinPrimeSegments (by decide : 4194349 ≤ 4325421)
    (by decide : 4325421 ≤ 4456493) S002C00.total S002C01.total

theorem join_0_1 : (twinPrimeSegment 4456493 4718637).card = 1463 := by
  simpa using combineTwinPrimeSegments (by decide : 4456493 ≤ 4587565)
    (by decide : 4587565 ≤ 4718637) S002C02.total S002C03.total

theorem join_0_2 : (twinPrimeSegment 4718637 4980781).card = 1436 := by
  simpa using combineTwinPrimeSegments (by decide : 4718637 ≤ 4849709)
    (by decide : 4849709 ≤ 4980781) S002C04.total S002C05.total

theorem join_0_3 : (twinPrimeSegment 4980781 5242925).card = 1393 := by
  simpa using combineTwinPrimeSegments (by decide : 4980781 ≤ 5111853)
    (by decide : 5111853 ≤ 5242925) S002C06.total S002C07.total

theorem join_0_4 : (twinPrimeSegment 5242925 5505069).card = 1452 := by
  simpa using combineTwinPrimeSegments (by decide : 5242925 ≤ 5373997)
    (by decide : 5373997 ≤ 5505069) S002C08.total S002C09.total

theorem join_0_5 : (twinPrimeSegment 5505069 5767213).card = 1431 := by
  simpa using combineTwinPrimeSegments (by decide : 5505069 ≤ 5636141)
    (by decide : 5636141 ≤ 5767213) S002C10.total S002C11.total

theorem join_0_6 : (twinPrimeSegment 5767213 6029357).card = 1456 := by
  simpa using combineTwinPrimeSegments (by decide : 5767213 ≤ 5898285)
    (by decide : 5898285 ≤ 6029357) S002C12.total S002C13.total

theorem join_0_7 : (twinPrimeSegment 6029357 6291501).card = 1438 := by
  simpa using combineTwinPrimeSegments (by decide : 6029357 ≤ 6160429)
    (by decide : 6160429 ≤ 6291501) S002C14.total S002C15.total

theorem join_1_0 : (twinPrimeSegment 4194349 4718637).card = 2929 := by
  simpa using combineTwinPrimeSegments (by decide : 4194349 ≤ 4456493)
    (by decide : 4456493 ≤ 4718637) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 4718637 5242925).card = 2829 := by
  simpa using combineTwinPrimeSegments (by decide : 4718637 ≤ 4980781)
    (by decide : 4980781 ≤ 5242925) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 5242925 5767213).card = 2883 := by
  simpa using combineTwinPrimeSegments (by decide : 5242925 ≤ 5505069)
    (by decide : 5505069 ≤ 5767213) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 5767213 6291501).card = 2894 := by
  simpa using combineTwinPrimeSegments (by decide : 5767213 ≤ 6029357)
    (by decide : 6029357 ≤ 6291501) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 4194349 5242925).card = 5758 := by
  simpa using combineTwinPrimeSegments (by decide : 4194349 ≤ 4718637)
    (by decide : 4718637 ≤ 5242925) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 5242925 6291501).card = 5777 := by
  simpa using combineTwinPrimeSegments (by decide : 5242925 ≤ 5767213)
    (by decide : 5767213 ≤ 6291501) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 4194349 6291501).card = 11535 := by
  simpa using combineTwinPrimeSegments (by decide : 4194349 ≤ 5242925)
    (by decide : 5242925 ≤ 6291501) join_2_0 join_2_1

theorem total : (twinPrimeSegment 4194349 6291501).card = 11535 := join_3_0

end S002All
end Sude.GeneratedTwinScan
