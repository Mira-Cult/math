import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18750)) 351535149 351567917 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 351535149 351567917).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18750 351535149 351567917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18751)) 351567917 351600685 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 351567917 351600685).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18751 351567917 351600685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18751)) 351600685 351633453 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 351600685 351633453).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18751 351600685 351633453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18752)) 351633453 351666221 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 351633453 351666221).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18752 351633453 351666221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 351535149 351600685).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 351535149 ≤ 351567917)
    (by decide : 351567917 ≤ 351600685) block0 block1

theorem join_0_1 : (twinPrimeSegment 351600685 351666221).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 351600685 ≤ 351633453)
    (by decide : 351633453 ≤ 351666221) block2 block3

theorem join_1_0 : (twinPrimeSegment 351535149 351666221).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 351535149 ≤ 351600685)
    (by decide : 351600685 ≤ 351666221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 351535149 351666221).card = 428 := join_1_0

end S167C10
end Sude.GeneratedTwinScan
