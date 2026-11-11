import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19487)) 379715629 379748397 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 379715629 379748397).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19487 379715629 379748397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19487)) 379748397 379781165 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 379748397 379781165).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19487 379748397 379781165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19488)) 379781165 379813933 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 379781165 379813933).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19488 379781165 379813933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19489)) 379813933 379846701 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 379813933 379846701).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19489 379813933 379846701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 379715629 379781165).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 379715629 ≤ 379748397)
    (by decide : 379748397 ≤ 379781165) block0 block1

theorem join_0_1 : (twinPrimeSegment 379781165 379846701).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 379781165 ≤ 379813933)
    (by decide : 379813933 ≤ 379846701) block2 block3

theorem join_1_0 : (twinPrimeSegment 379715629 379846701).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 379715629 ≤ 379781165)
    (by decide : 379781165 ≤ 379846701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 379715629 379846701).card = 456 := join_1_0

end S181C01
end Sude.GeneratedTwinScan
