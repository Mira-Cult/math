import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15694)) 246284333 246317101 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 246284333 246317101).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15694 246284333 246317101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15695)) 246317101 246349869 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 246317101 246349869).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15695 246317101 246349869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15696)) 246349869 246382637 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 246349869 246382637).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15696 246349869 246382637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15697)) 246382637 246415405 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 246382637 246415405).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15697 246382637 246415405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 246284333 246349869).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 246284333 ≤ 246317101)
    (by decide : 246317101 ≤ 246349869) block0 block1

theorem join_0_1 : (twinPrimeSegment 246349869 246415405).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 246349869 ≤ 246382637)
    (by decide : 246382637 ≤ 246415405) block2 block3

theorem join_1_0 : (twinPrimeSegment 246284333 246415405).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 246284333 ≤ 246349869)
    (by decide : 246349869 ≤ 246415405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 246284333 246415405).card = 456 := join_1_0

end S117C07
end Sude.GeneratedTwinScan
