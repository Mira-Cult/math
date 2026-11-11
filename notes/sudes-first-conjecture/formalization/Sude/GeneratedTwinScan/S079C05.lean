import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12898)) 166330413 166363181 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 166330413 166363181).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12898 166330413 166363181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12899)) 166363181 166395949 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 166363181 166395949).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12899 166363181 166395949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12900)) 166395949 166428717 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 166395949 166428717).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12900 166395949 166428717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12901)) 166428717 166461485 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 166428717 166461485).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12901 166428717 166461485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 166330413 166395949).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 166330413 ≤ 166363181)
    (by decide : 166363181 ≤ 166395949) block0 block1

theorem join_0_1 : (twinPrimeSegment 166395949 166461485).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 166395949 ≤ 166428717)
    (by decide : 166428717 ≤ 166461485) block2 block3

theorem join_1_0 : (twinPrimeSegment 166330413 166461485).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 166330413 ≤ 166395949)
    (by decide : 166395949 ≤ 166461485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 166330413 166461485).card = 490 := join_1_0

end S079C05
end Sude.GeneratedTwinScan
