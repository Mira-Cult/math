import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19399)) 376307757 376340525 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 376307757 376340525).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19399 376307757 376340525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19400)) 376340525 376373293 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 376340525 376373293).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19400 376340525 376373293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19401)) 376373293 376406061 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 376373293 376406061).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19401 376373293 376406061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19402)) 376406061 376438829 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 376406061 376438829).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19402 376406061 376438829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 376307757 376373293).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 376307757 ≤ 376340525)
    (by decide : 376340525 ≤ 376373293) block0 block1

theorem join_0_1 : (twinPrimeSegment 376373293 376438829).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 376373293 ≤ 376406061)
    (by decide : 376406061 ≤ 376438829) block2 block3

theorem join_1_0 : (twinPrimeSegment 376307757 376438829).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 376307757 ≤ 376373293)
    (by decide : 376373293 ≤ 376438829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 376307757 376438829).card = 422 := join_1_0

end S179C07
end Sude.GeneratedTwinScan
