import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17525)) 307101741 307134509 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 307101741 307134509).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17525 307101741 307134509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17526)) 307134509 307167277 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 307134509 307167277).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17526 307134509 307167277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17527)) 307167277 307200045 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 307167277 307200045).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17527 307167277 307200045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17528)) 307200045 307232813 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 307200045 307232813).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17528 307200045 307232813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 307101741 307167277).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 307101741 ≤ 307134509)
    (by decide : 307134509 ≤ 307167277) block0 block1

theorem join_0_1 : (twinPrimeSegment 307167277 307232813).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 307167277 ≤ 307200045)
    (by decide : 307200045 ≤ 307232813) block2 block3

theorem join_1_0 : (twinPrimeSegment 307101741 307232813).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 307101741 ≤ 307167277)
    (by decide : 307167277 ≤ 307232813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 307101741 307232813).card = 456 := join_1_0

end S146C07
end Sude.GeneratedTwinScan
