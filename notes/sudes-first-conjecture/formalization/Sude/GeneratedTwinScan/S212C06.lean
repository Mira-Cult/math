import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21104)) 445382701 445415469 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 445382701 445415469).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21104 445382701 445415469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21105)) 445415469 445448237 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 445415469 445448237).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21105 445415469 445448237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21106)) 445448237 445481005 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 445448237 445481005).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21106 445448237 445481005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21107)) 445481005 445513773 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 445481005 445513773).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21107 445481005 445513773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 445382701 445448237).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 445382701 ≤ 445415469)
    (by decide : 445415469 ≤ 445448237) block0 block1

theorem join_0_1 : (twinPrimeSegment 445448237 445513773).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 445448237 ≤ 445481005)
    (by decide : 445481005 ≤ 445513773) block2 block3

theorem join_1_0 : (twinPrimeSegment 445382701 445513773).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 445382701 ≤ 445448237)
    (by decide : 445448237 ≤ 445513773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 445382701 445513773).card = 432 := join_1_0

end S212C06
end Sude.GeneratedTwinScan
