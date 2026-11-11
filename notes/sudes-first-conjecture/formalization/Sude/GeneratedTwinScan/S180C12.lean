import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19470)) 379060269 379093037 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 379060269 379093037).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19470 379060269 379093037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19471)) 379093037 379125805 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 379093037 379125805).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19471 379093037 379125805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19471)) 379125805 379158573 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 379125805 379158573).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19471 379125805 379158573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19472)) 379158573 379191341 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 379158573 379191341).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19472 379158573 379191341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 379060269 379125805).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 379060269 ≤ 379093037)
    (by decide : 379093037 ≤ 379125805) block0 block1

theorem join_0_1 : (twinPrimeSegment 379125805 379191341).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 379125805 ≤ 379158573)
    (by decide : 379158573 ≤ 379191341) block2 block3

theorem join_1_0 : (twinPrimeSegment 379060269 379191341).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 379060269 ≤ 379125805)
    (by decide : 379125805 ≤ 379191341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 379060269 379191341).card = 454 := join_1_0

end S180C12
end Sude.GeneratedTwinScan
