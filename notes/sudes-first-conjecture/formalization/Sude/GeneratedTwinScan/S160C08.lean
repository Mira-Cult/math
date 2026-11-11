import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18347)) 336592941 336625709 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 336592941 336625709).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18347 336592941 336625709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18348)) 336625709 336658477 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 336625709 336658477).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18348 336625709 336658477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18349)) 336658477 336691245 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 336658477 336691245).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18349 336658477 336691245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18350)) 336691245 336724013 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 336691245 336724013).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18350 336691245 336724013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 336592941 336658477).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 336592941 ≤ 336625709)
    (by decide : 336625709 ≤ 336658477) block0 block1

theorem join_0_1 : (twinPrimeSegment 336658477 336724013).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 336658477 ≤ 336691245)
    (by decide : 336691245 ≤ 336724013) block2 block3

theorem join_1_0 : (twinPrimeSegment 336592941 336724013).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 336592941 ≤ 336658477)
    (by decide : 336658477 ≤ 336724013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 336592941 336724013).card = 454 := join_1_0

end S160C08
end Sude.GeneratedTwinScan
