import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22250)) 495058989 495091757 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 495058989 495091757).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22250 495058989 495091757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22251)) 495091757 495124525 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 495091757 495124525).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22251 495091757 495124525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22252)) 495124525 495157293 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 495124525 495157293).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22252 495124525 495157293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22252)) 495157293 495190061 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 495157293 495190061).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22252 495157293 495190061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 495058989 495124525).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 495058989 ≤ 495091757)
    (by decide : 495091757 ≤ 495124525) block0 block1

theorem join_0_1 : (twinPrimeSegment 495124525 495190061).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 495124525 ≤ 495157293)
    (by decide : 495157293 ≤ 495190061) block2 block3

theorem join_1_0 : (twinPrimeSegment 495058989 495190061).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 495058989 ≤ 495124525)
    (by decide : 495124525 ≤ 495190061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 495058989 495190061).card = 439 := join_1_0

end S236C01
end Sude.GeneratedTwinScan
