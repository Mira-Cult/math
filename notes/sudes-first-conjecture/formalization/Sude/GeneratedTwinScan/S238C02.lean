import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22347)) 499384365 499417133 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 499384365 499417133).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22347 499384365 499417133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22348)) 499417133 499449901 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 499417133 499449901).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22348 499417133 499449901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22349)) 499449901 499482669 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 499449901 499482669).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22349 499449901 499482669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22349)) 499482669 499515437 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 499482669 499515437).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22349 499482669 499515437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 499384365 499449901).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 499384365 ≤ 499417133)
    (by decide : 499417133 ≤ 499449901) block0 block1

theorem join_0_1 : (twinPrimeSegment 499449901 499515437).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 499449901 ≤ 499482669)
    (by decide : 499482669 ≤ 499515437) block2 block3

theorem join_1_0 : (twinPrimeSegment 499384365 499515437).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 499384365 ≤ 499449901)
    (by decide : 499449901 ≤ 499515437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 499384365 499515437).card = 449 := join_1_0

end S238C02
end Sude.GeneratedTwinScan
