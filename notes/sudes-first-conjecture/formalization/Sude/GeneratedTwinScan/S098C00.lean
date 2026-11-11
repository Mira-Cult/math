import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14337)) 205520941 205553709 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 205520941 205553709).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14337 205520941 205553709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14338)) 205553709 205586477 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 205553709 205586477).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14338 205553709 205586477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14339)) 205586477 205619245 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 205586477 205619245).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14339 205586477 205619245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14340)) 205619245 205652013 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 205619245 205652013).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14340 205619245 205652013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 205520941 205586477).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 205520941 ≤ 205553709)
    (by decide : 205553709 ≤ 205586477) block0 block1

theorem join_0_1 : (twinPrimeSegment 205586477 205652013).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 205586477 ≤ 205619245)
    (by decide : 205619245 ≤ 205652013) block2 block3

theorem join_1_0 : (twinPrimeSegment 205520941 205652013).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 205520941 ≤ 205586477)
    (by decide : 205586477 ≤ 205652013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 205520941 205652013).card = 464 := join_1_0

end S098C00
end Sude.GeneratedTwinScan
