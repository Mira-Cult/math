import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21792)) 474873901 474906669 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 474873901 474906669).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21792 474873901 474906669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21793)) 474906669 474939437 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 474906669 474939437).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21793 474906669 474939437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21793)) 474939437 474972205 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 474939437 474972205).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21793 474939437 474972205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21794)) 474972205 475004973 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 474972205 475004973).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21794 474972205 475004973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 474873901 474939437).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 474873901 ≤ 474906669)
    (by decide : 474906669 ≤ 474939437) block0 block1

theorem join_0_1 : (twinPrimeSegment 474939437 475004973).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 474939437 ≤ 474972205)
    (by decide : 474972205 ≤ 475004973) block2 block3

theorem join_1_0 : (twinPrimeSegment 474873901 475004973).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 474873901 ≤ 474939437)
    (by decide : 474939437 ≤ 475004973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 474873901 475004973).card = 460 := join_1_0

end S226C07
end Sude.GeneratedTwinScan
