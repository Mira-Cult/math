import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22883)) 523632685 523665453 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 523632685 523665453).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22883 523632685 523665453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22884)) 523665453 523698221 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 523665453 523698221).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22884 523665453 523698221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22885)) 523698221 523730989 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 523698221 523730989).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22885 523698221 523730989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22885)) 523730989 523763757 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 523730989 523763757).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22885 523730989 523763757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 523632685 523698221).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 523632685 ≤ 523665453)
    (by decide : 523665453 ≤ 523698221) block0 block1

theorem join_0_1 : (twinPrimeSegment 523698221 523763757).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 523698221 ≤ 523730989)
    (by decide : 523730989 ≤ 523763757) block2 block3

theorem join_1_0 : (twinPrimeSegment 523632685 523763757).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 523632685 ≤ 523698221)
    (by decide : 523698221 ≤ 523763757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 523632685 523763757).card = 420 := join_1_0

end S249C11
end Sude.GeneratedTwinScan
