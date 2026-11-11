import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16360)) 267649069 267681837 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 267649069 267681837).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16360 267649069 267681837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16361)) 267681837 267714605 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 267681837 267714605).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16361 267681837 267714605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16362)) 267714605 267747373 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 267714605 267747373).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16362 267714605 267747373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16363)) 267747373 267780141 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 267747373 267780141).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16363 267747373 267780141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 267649069 267714605).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 267649069 ≤ 267681837)
    (by decide : 267681837 ≤ 267714605) block0 block1

theorem join_0_1 : (twinPrimeSegment 267714605 267780141).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 267714605 ≤ 267747373)
    (by decide : 267747373 ≤ 267780141) block2 block3

theorem join_1_0 : (twinPrimeSegment 267649069 267780141).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 267649069 ≤ 267714605)
    (by decide : 267714605 ≤ 267780141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 267649069 267780141).card = 435 := join_1_0

end S127C10
end Sude.GeneratedTwinScan
