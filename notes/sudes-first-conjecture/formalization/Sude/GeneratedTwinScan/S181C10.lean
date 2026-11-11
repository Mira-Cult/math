import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19517)) 380895277 380928045 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 380895277 380928045).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19517 380895277 380928045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19518)) 380928045 380960813 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 380928045 380960813).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19518 380928045 380960813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19519)) 380960813 380993581 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 380960813 380993581).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19519 380960813 380993581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19519)) 380993581 381026349 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 380993581 381026349).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19519 380993581 381026349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 380895277 380960813).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 380895277 ≤ 380928045)
    (by decide : 380928045 ≤ 380960813) block0 block1

theorem join_0_1 : (twinPrimeSegment 380960813 381026349).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 380960813 ≤ 380993581)
    (by decide : 380993581 ≤ 381026349) block2 block3

theorem join_1_0 : (twinPrimeSegment 380895277 381026349).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 380895277 ≤ 380960813)
    (by decide : 380960813 ≤ 381026349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 380895277 381026349).card = 438 := join_1_0

end S181C10
end Sude.GeneratedTwinScan
