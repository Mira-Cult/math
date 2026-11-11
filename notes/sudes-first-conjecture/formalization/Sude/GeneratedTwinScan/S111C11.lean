import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15305)) 234225709 234258477 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 234225709 234258477).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15305 234225709 234258477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15306)) 234258477 234291245 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 234258477 234291245).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15306 234258477 234291245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15307)) 234291245 234324013 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 234291245 234324013).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15307 234291245 234324013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15308)) 234324013 234356781 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 234324013 234356781).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15308 234324013 234356781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 234225709 234291245).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 234225709 ≤ 234258477)
    (by decide : 234258477 ≤ 234291245) block0 block1

theorem join_0_1 : (twinPrimeSegment 234291245 234356781).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 234291245 ≤ 234324013)
    (by decide : 234324013 ≤ 234356781) block2 block3

theorem join_1_0 : (twinPrimeSegment 234225709 234356781).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 234225709 ≤ 234291245)
    (by decide : 234291245 ≤ 234356781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 234225709 234356781).card = 461 := join_1_0

end S111C11
end Sude.GeneratedTwinScan
