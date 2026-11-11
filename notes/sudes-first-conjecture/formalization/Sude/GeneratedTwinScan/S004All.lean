import Sude.GeneratedTwinScan.S004C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S004All

theorem join_0_0 : (twinPrimeSegment 8388653 8650797).card = 1424 := by
  simpa using combineTwinPrimeSegments (by decide : 8388653 ≤ 8519725)
    (by decide : 8519725 ≤ 8650797) S004C00.total S004C01.total

theorem join_0_1 : (twinPrimeSegment 8650797 8912941).card = 1340 := by
  simpa using combineTwinPrimeSegments (by decide : 8650797 ≤ 8781869)
    (by decide : 8781869 ≤ 8912941) S004C02.total S004C03.total

theorem join_0_2 : (twinPrimeSegment 8912941 9175085).card = 1347 := by
  simpa using combineTwinPrimeSegments (by decide : 8912941 ≤ 9044013)
    (by decide : 9044013 ≤ 9175085) S004C04.total S004C05.total

theorem join_0_3 : (twinPrimeSegment 9175085 9437229).card = 1340 := by
  simpa using combineTwinPrimeSegments (by decide : 9175085 ≤ 9306157)
    (by decide : 9306157 ≤ 9437229) S004C06.total S004C07.total

theorem join_0_4 : (twinPrimeSegment 9437229 9699373).card = 1360 := by
  simpa using combineTwinPrimeSegments (by decide : 9437229 ≤ 9568301)
    (by decide : 9568301 ≤ 9699373) S004C08.total S004C09.total

theorem join_0_5 : (twinPrimeSegment 9699373 9961517).card = 1339 := by
  simpa using combineTwinPrimeSegments (by decide : 9699373 ≤ 9830445)
    (by decide : 9830445 ≤ 9961517) S004C10.total S004C11.total

theorem join_0_6 : (twinPrimeSegment 9961517 10223661).card = 1352 := by
  simpa using combineTwinPrimeSegments (by decide : 9961517 ≤ 10092589)
    (by decide : 10092589 ≤ 10223661) S004C12.total S004C13.total

theorem join_0_7 : (twinPrimeSegment 10223661 10485805).card = 1321 := by
  simpa using combineTwinPrimeSegments (by decide : 10223661 ≤ 10354733)
    (by decide : 10354733 ≤ 10485805) S004C14.total S004C15.total

theorem join_1_0 : (twinPrimeSegment 8388653 8912941).card = 2764 := by
  simpa using combineTwinPrimeSegments (by decide : 8388653 ≤ 8650797)
    (by decide : 8650797 ≤ 8912941) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 8912941 9437229).card = 2687 := by
  simpa using combineTwinPrimeSegments (by decide : 8912941 ≤ 9175085)
    (by decide : 9175085 ≤ 9437229) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 9437229 9961517).card = 2699 := by
  simpa using combineTwinPrimeSegments (by decide : 9437229 ≤ 9699373)
    (by decide : 9699373 ≤ 9961517) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 9961517 10485805).card = 2673 := by
  simpa using combineTwinPrimeSegments (by decide : 9961517 ≤ 10223661)
    (by decide : 10223661 ≤ 10485805) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 8388653 9437229).card = 5451 := by
  simpa using combineTwinPrimeSegments (by decide : 8388653 ≤ 8912941)
    (by decide : 8912941 ≤ 9437229) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 9437229 10485805).card = 5372 := by
  simpa using combineTwinPrimeSegments (by decide : 9437229 ≤ 9961517)
    (by decide : 9961517 ≤ 10485805) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 8388653 10485805).card = 10823 := by
  simpa using combineTwinPrimeSegments (by decide : 8388653 ≤ 9437229)
    (by decide : 9437229 ≤ 10485805) join_2_0 join_2_1

theorem total : (twinPrimeSegment 8388653 10485805).card = 10823 := join_3_0

end S004All
end Sude.GeneratedTwinScan
