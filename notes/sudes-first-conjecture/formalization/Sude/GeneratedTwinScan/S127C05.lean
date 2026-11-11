import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16340)) 266993709 267026477 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 266993709 267026477).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16340 266993709 267026477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16341)) 267026477 267059245 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 267026477 267059245).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16341 267026477 267059245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16342)) 267059245 267092013 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 267059245 267092013).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16342 267059245 267092013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16343)) 267092013 267124781 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 267092013 267124781).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16343 267092013 267124781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 266993709 267059245).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 266993709 ≤ 267026477)
    (by decide : 267026477 ≤ 267059245) block0 block1

theorem join_0_1 : (twinPrimeSegment 267059245 267124781).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 267059245 ≤ 267092013)
    (by decide : 267092013 ≤ 267124781) block2 block3

theorem join_1_0 : (twinPrimeSegment 266993709 267124781).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 266993709 ≤ 267059245)
    (by decide : 267059245 ≤ 267124781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 266993709 267124781).card = 458 := join_1_0

end S127C05
end Sude.GeneratedTwinScan
