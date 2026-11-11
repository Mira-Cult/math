import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18012)) 324403245 324436013 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 324403245 324436013).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18012 324403245 324436013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18013)) 324436013 324468781 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 324436013 324468781).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18013 324436013 324468781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18013)) 324468781 324501549 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 324468781 324501549).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18013 324468781 324501549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18014)) 324501549 324534317 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 324501549 324534317).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18014 324501549 324534317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 324403245 324468781).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 324403245 ≤ 324436013)
    (by decide : 324436013 ≤ 324468781) block0 block1

theorem join_0_1 : (twinPrimeSegment 324468781 324534317).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 324468781 ≤ 324501549)
    (by decide : 324501549 ≤ 324534317) block2 block3

theorem join_1_0 : (twinPrimeSegment 324403245 324534317).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 324403245 ≤ 324468781)
    (by decide : 324468781 ≤ 324534317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 324403245 324534317).card = 493 := join_1_0

end S154C11
end Sude.GeneratedTwinScan
