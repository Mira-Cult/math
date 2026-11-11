import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15111)) 228327469 228360237 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 228327469 228360237).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15111 228327469 228360237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15112)) 228360237 228393005 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 228360237 228393005).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15112 228360237 228393005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15113)) 228393005 228425773 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 228393005 228425773).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15113 228393005 228425773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15114)) 228425773 228458541 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 228425773 228458541).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15114 228425773 228458541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 228327469 228393005).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 228327469 ≤ 228360237)
    (by decide : 228360237 ≤ 228393005) block0 block1

theorem join_0_1 : (twinPrimeSegment 228393005 228458541).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 228393005 ≤ 228425773)
    (by decide : 228425773 ≤ 228458541) block2 block3

theorem join_1_0 : (twinPrimeSegment 228327469 228458541).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 228327469 ≤ 228393005)
    (by decide : 228393005 ≤ 228458541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 228327469 228458541).card = 471 := join_1_0

end S108C14
end Sude.GeneratedTwinScan
