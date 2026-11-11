import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14013)) 196345901 196378669 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 196345901 196378669).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14013 196345901 196378669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14014)) 196378669 196411437 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 196378669 196411437).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14014 196378669 196411437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14015)) 196411437 196444205 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 196411437 196444205).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14015 196411437 196444205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14017)) 196444205 196476973 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 196444205 196476973).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14017 196444205 196476973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 196345901 196411437).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 196345901 ≤ 196378669)
    (by decide : 196378669 ≤ 196411437) block0 block1

theorem join_0_1 : (twinPrimeSegment 196411437 196476973).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 196411437 ≤ 196444205)
    (by decide : 196444205 ≤ 196476973) block2 block3

theorem join_1_0 : (twinPrimeSegment 196345901 196476973).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 196345901 ≤ 196411437)
    (by decide : 196411437 ≤ 196476973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 196345901 196476973).card = 441 := join_1_0

end S093C10
end Sude.GeneratedTwinScan
