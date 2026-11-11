import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12411)) 154009645 154042413 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 154009645 154042413).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12411 154009645 154042413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12412)) 154042413 154075181 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 154042413 154075181).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12412 154042413 154075181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12414)) 154075181 154107949 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 154075181 154107949).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12414 154075181 154107949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12415)) 154107949 154140717 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 154107949 154140717).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12415 154107949 154140717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 154009645 154075181).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 154009645 ≤ 154042413)
    (by decide : 154042413 ≤ 154075181) block0 block1

theorem join_0_1 : (twinPrimeSegment 154075181 154140717).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 154075181 ≤ 154107949)
    (by decide : 154107949 ≤ 154140717) block2 block3

theorem join_1_0 : (twinPrimeSegment 154009645 154140717).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 154009645 ≤ 154075181)
    (by decide : 154075181 ≤ 154140717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 154009645 154140717).card = 491 := join_1_0

end S073C07
end Sude.GeneratedTwinScan
