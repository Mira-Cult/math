import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22238)) 494534701 494567469 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 494534701 494567469).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22238 494534701 494567469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22239)) 494567469 494600237 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 494567469 494600237).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22239 494567469 494600237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22240)) 494600237 494633005 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 494600237 494633005).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22240 494600237 494633005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22241)) 494633005 494665773 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 494633005 494665773).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22241 494633005 494665773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 494534701 494600237).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 494534701 ≤ 494567469)
    (by decide : 494567469 ≤ 494600237) block0 block1

theorem join_0_1 : (twinPrimeSegment 494600237 494665773).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 494600237 ≤ 494633005)
    (by decide : 494633005 ≤ 494665773) block2 block3

theorem join_1_0 : (twinPrimeSegment 494534701 494665773).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 494534701 ≤ 494600237)
    (by decide : 494600237 ≤ 494665773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 494534701 494665773).card = 415 := join_1_0

end S235C13
end Sude.GeneratedTwinScan
