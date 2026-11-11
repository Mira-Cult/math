import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22262)) 495583277 495616045 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 495583277 495616045).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22262 495583277 495616045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22263)) 495616045 495648813 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 495616045 495648813).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22263 495616045 495648813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22263)) 495648813 495681581 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 495648813 495681581).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22263 495648813 495681581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22264)) 495681581 495714349 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 495681581 495714349).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22264 495681581 495714349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 495583277 495648813).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 495583277 ≤ 495616045)
    (by decide : 495616045 ≤ 495648813) block0 block1

theorem join_0_1 : (twinPrimeSegment 495648813 495714349).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 495648813 ≤ 495681581)
    (by decide : 495681581 ≤ 495714349) block2 block3

theorem join_1_0 : (twinPrimeSegment 495583277 495714349).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 495583277 ≤ 495648813)
    (by decide : 495648813 ≤ 495714349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 495583277 495714349).card = 432 := join_1_0

end S236C05
end Sude.GeneratedTwinScan
