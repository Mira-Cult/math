import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22247)) 494927917 494960685 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 494927917 494960685).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22247 494927917 494960685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22248)) 494960685 494993453 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 494960685 494993453).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22248 494960685 494993453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22249)) 494993453 495026221 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 494993453 495026221).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22249 494993453 495026221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22249)) 495026221 495058989 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 495026221 495058989).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22249 495026221 495058989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 494927917 494993453).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 494927917 ≤ 494960685)
    (by decide : 494960685 ≤ 494993453) block0 block1

theorem join_0_1 : (twinPrimeSegment 494993453 495058989).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 494993453 ≤ 495026221)
    (by decide : 495026221 ≤ 495058989) block2 block3

theorem join_1_0 : (twinPrimeSegment 494927917 495058989).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 494927917 ≤ 494993453)
    (by decide : 494993453 ≤ 495058989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 494927917 495058989).card = 431 := join_1_0

end S236C00
end Sude.GeneratedTwinScan
