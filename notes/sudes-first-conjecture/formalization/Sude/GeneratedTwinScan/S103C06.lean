import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14725)) 216793133 216825901 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 216793133 216825901).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14725 216793133 216825901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14726)) 216825901 216858669 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 216825901 216858669).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14726 216825901 216858669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14727)) 216858669 216891437 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 216858669 216891437).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14727 216858669 216891437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14728)) 216891437 216924205 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 216891437 216924205).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14728 216891437 216924205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 216793133 216858669).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 216793133 ≤ 216825901)
    (by decide : 216825901 ≤ 216858669) block0 block1

theorem join_0_1 : (twinPrimeSegment 216858669 216924205).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 216858669 ≤ 216891437)
    (by decide : 216891437 ≤ 216924205) block2 block3

theorem join_1_0 : (twinPrimeSegment 216793133 216924205).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 216793133 ≤ 216858669)
    (by decide : 216858669 ≤ 216924205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 216793133 216924205).card = 454 := join_1_0

end S103C06
end Sude.GeneratedTwinScan
