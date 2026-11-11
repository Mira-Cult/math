import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19524)) 381157421 381190189 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 381157421 381190189).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19524 381157421 381190189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19524)) 381190189 381222957 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 381190189 381222957).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19524 381190189 381222957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19525)) 381222957 381255725 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 381222957 381255725).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19525 381222957 381255725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19526)) 381255725 381288493 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 381255725 381288493).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19526 381255725 381288493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 381157421 381222957).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 381157421 ≤ 381190189)
    (by decide : 381190189 ≤ 381222957) block0 block1

theorem join_0_1 : (twinPrimeSegment 381222957 381288493).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 381222957 ≤ 381255725)
    (by decide : 381255725 ≤ 381288493) block2 block3

theorem join_1_0 : (twinPrimeSegment 381157421 381288493).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 381157421 ≤ 381222957)
    (by decide : 381222957 ≤ 381288493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 381157421 381288493).card = 441 := join_1_0

end S181C12
end Sude.GeneratedTwinScan
