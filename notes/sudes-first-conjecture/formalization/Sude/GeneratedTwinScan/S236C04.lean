import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22259)) 495452205 495484973 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 495452205 495484973).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22259 495452205 495484973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22260)) 495484973 495517741 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 495484973 495517741).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22260 495484973 495517741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22260)) 495517741 495550509 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 495517741 495550509).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22260 495517741 495550509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22261)) 495550509 495583277 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 495550509 495583277).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22261 495550509 495583277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 495452205 495517741).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 495452205 ≤ 495484973)
    (by decide : 495484973 ≤ 495517741) block0 block1

theorem join_0_1 : (twinPrimeSegment 495517741 495583277).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 495517741 ≤ 495550509)
    (by decide : 495550509 ≤ 495583277) block2 block3

theorem join_1_0 : (twinPrimeSegment 495452205 495583277).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 495452205 ≤ 495517741)
    (by decide : 495517741 ≤ 495583277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 495452205 495583277).card = 419 := join_1_0

end S236C04
end Sude.GeneratedTwinScan
