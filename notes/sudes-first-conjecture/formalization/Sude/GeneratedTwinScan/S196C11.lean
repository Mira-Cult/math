import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20310)) 412483629 412516397 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 412483629 412516397).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20310 412483629 412516397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20311)) 412516397 412549165 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 412516397 412549165).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20311 412516397 412549165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20312)) 412549165 412581933 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 412549165 412581933).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20312 412549165 412581933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20312)) 412581933 412614701 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 412581933 412614701).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20312 412581933 412614701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 412483629 412549165).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 412483629 ≤ 412516397)
    (by decide : 412516397 ≤ 412549165) block0 block1

theorem join_0_1 : (twinPrimeSegment 412549165 412614701).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 412549165 ≤ 412581933)
    (by decide : 412581933 ≤ 412614701) block2 block3

theorem join_1_0 : (twinPrimeSegment 412483629 412614701).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 412483629 ≤ 412549165)
    (by decide : 412549165 ≤ 412614701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 412483629 412614701).card = 428 := join_1_0

end S196C11
end Sude.GeneratedTwinScan
