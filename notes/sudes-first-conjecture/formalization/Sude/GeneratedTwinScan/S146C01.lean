import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17502)) 306315309 306348077 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 306315309 306348077).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17502 306315309 306348077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17503)) 306348077 306380845 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 306348077 306380845).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17503 306348077 306380845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17504)) 306380845 306413613 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 306380845 306413613).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17504 306380845 306413613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17505)) 306413613 306446381 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 306413613 306446381).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17505 306413613 306446381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 306315309 306380845).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 306315309 ≤ 306348077)
    (by decide : 306348077 ≤ 306380845) block0 block1

theorem join_0_1 : (twinPrimeSegment 306380845 306446381).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 306380845 ≤ 306413613)
    (by decide : 306413613 ≤ 306446381) block2 block3

theorem join_1_0 : (twinPrimeSegment 306315309 306446381).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 306315309 ≤ 306380845)
    (by decide : 306380845 ≤ 306446381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 306315309 306446381).card = 430 := join_1_0

end S146C01
end Sude.GeneratedTwinScan
