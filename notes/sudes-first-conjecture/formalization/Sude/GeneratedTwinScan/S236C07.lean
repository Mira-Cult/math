import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22268)) 495845421 495878189 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 495845421 495878189).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22268 495845421 495878189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22269)) 495878189 495910957 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 495878189 495910957).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22269 495878189 495910957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22269)) 495910957 495943725 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 495910957 495943725).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22269 495910957 495943725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22270)) 495943725 495976493 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 495943725 495976493).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22270 495943725 495976493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 495845421 495910957).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 495845421 ≤ 495878189)
    (by decide : 495878189 ≤ 495910957) block0 block1

theorem join_0_1 : (twinPrimeSegment 495910957 495976493).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 495910957 ≤ 495943725)
    (by decide : 495943725 ≤ 495976493) block2 block3

theorem join_1_0 : (twinPrimeSegment 495845421 495976493).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 495845421 ≤ 495910957)
    (by decide : 495910957 ≤ 495976493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 495845421 495976493).card = 438 := join_1_0

end S236C07
end Sude.GeneratedTwinScan
