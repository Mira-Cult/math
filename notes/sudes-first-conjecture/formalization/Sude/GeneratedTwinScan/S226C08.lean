import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21795)) 475004973 475037741 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 475004973 475037741).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21795 475004973 475037741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21796)) 475037741 475070509 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 475037741 475070509).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21796 475037741 475070509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21796)) 475070509 475103277 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 475070509 475103277).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21796 475070509 475103277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21797)) 475103277 475136045 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 475103277 475136045).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21797 475103277 475136045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 475004973 475070509).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 475004973 ≤ 475037741)
    (by decide : 475037741 ≤ 475070509) block0 block1

theorem join_0_1 : (twinPrimeSegment 475070509 475136045).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 475070509 ≤ 475103277)
    (by decide : 475103277 ≤ 475136045) block2 block3

theorem join_1_0 : (twinPrimeSegment 475004973 475136045).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 475004973 ≤ 475070509)
    (by decide : 475070509 ≤ 475136045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 475004973 475136045).card = 414 := join_1_0

end S226C08
end Sude.GeneratedTwinScan
