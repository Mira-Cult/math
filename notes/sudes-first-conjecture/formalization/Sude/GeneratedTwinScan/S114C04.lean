import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15480)) 239599661 239632429 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 239599661 239632429).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15480 239599661 239632429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15481)) 239632429 239665197 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 239632429 239665197).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15481 239632429 239665197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15482)) 239665197 239697965 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 239665197 239697965).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15482 239665197 239697965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15483)) 239697965 239730733 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 239697965 239730733).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15483 239697965 239730733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 239599661 239665197).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 239599661 ≤ 239632429)
    (by decide : 239632429 ≤ 239665197) block0 block1

theorem join_0_1 : (twinPrimeSegment 239665197 239730733).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 239665197 ≤ 239697965)
    (by decide : 239697965 ≤ 239730733) block2 block3

theorem join_1_0 : (twinPrimeSegment 239599661 239730733).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 239599661 ≤ 239665197)
    (by decide : 239665197 ≤ 239730733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 239599661 239730733).card = 456 := join_1_0

end S114C04
end Sude.GeneratedTwinScan
