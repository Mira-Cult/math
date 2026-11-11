import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17637)) 311033901 311066669 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 311033901 311066669).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17637 311033901 311066669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17638)) 311066669 311099437 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 311066669 311099437).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17638 311066669 311099437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17638)) 311099437 311132205 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 311099437 311132205).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17638 311099437 311132205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17639)) 311132205 311164973 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 311132205 311164973).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17639 311132205 311164973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 311033901 311099437).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 311033901 ≤ 311066669)
    (by decide : 311066669 ≤ 311099437) block0 block1

theorem join_0_1 : (twinPrimeSegment 311099437 311164973).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 311099437 ≤ 311132205)
    (by decide : 311132205 ≤ 311164973) block2 block3

theorem join_1_0 : (twinPrimeSegment 311033901 311164973).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 311033901 ≤ 311099437)
    (by decide : 311099437 ≤ 311164973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 311033901 311164973).card = 439 := join_1_0

end S148C05
end Sude.GeneratedTwinScan
