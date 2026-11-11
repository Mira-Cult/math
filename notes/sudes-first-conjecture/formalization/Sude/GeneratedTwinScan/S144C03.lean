import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17390)) 302383149 302415917 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 302383149 302415917).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17390 302383149 302415917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17391)) 302415917 302448685 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 302415917 302448685).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17391 302415917 302448685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17391)) 302448685 302481453 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 302448685 302481453).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17391 302448685 302481453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17392)) 302481453 302514221 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 302481453 302514221).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17392 302481453 302514221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 302383149 302448685).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 302383149 ≤ 302415917)
    (by decide : 302415917 ≤ 302448685) block0 block1

theorem join_0_1 : (twinPrimeSegment 302448685 302514221).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 302448685 ≤ 302481453)
    (by decide : 302481453 ≤ 302514221) block2 block3

theorem join_1_0 : (twinPrimeSegment 302383149 302514221).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 302383149 ≤ 302448685)
    (by decide : 302448685 ≤ 302514221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 302383149 302514221).card = 428 := join_1_0

end S144C03
end Sude.GeneratedTwinScan
