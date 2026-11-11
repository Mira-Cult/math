import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20245)) 409862189 409894957 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 409862189 409894957).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20245 409862189 409894957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20246)) 409894957 409927725 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 409894957 409927725).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20246 409894957 409927725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20247)) 409927725 409960493 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 409927725 409960493).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20247 409927725 409960493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20248)) 409960493 409993261 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 409960493 409993261).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20248 409960493 409993261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 409862189 409927725).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 409862189 ≤ 409894957)
    (by decide : 409894957 ≤ 409927725) block0 block1

theorem join_0_1 : (twinPrimeSegment 409927725 409993261).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 409927725 ≤ 409960493)
    (by decide : 409960493 ≤ 409993261) block2 block3

theorem join_1_0 : (twinPrimeSegment 409862189 409993261).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 409862189 ≤ 409927725)
    (by decide : 409927725 ≤ 409993261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 409862189 409993261).card = 437 := join_1_0

end S195C07
end Sude.GeneratedTwinScan
