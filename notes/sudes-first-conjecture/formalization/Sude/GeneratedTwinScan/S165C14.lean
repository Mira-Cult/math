import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18652)) 347865133 347897901 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 347865133 347897901).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18652 347865133 347897901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18652)) 347897901 347930669 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 347897901 347930669).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18652 347897901 347930669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18653)) 347930669 347963437 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 347930669 347963437).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18653 347930669 347963437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18654)) 347963437 347996205 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 347963437 347996205).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18654 347963437 347996205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 347865133 347930669).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 347865133 ≤ 347897901)
    (by decide : 347897901 ≤ 347930669) block0 block1

theorem join_0_1 : (twinPrimeSegment 347930669 347996205).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 347930669 ≤ 347963437)
    (by decide : 347963437 ≤ 347996205) block2 block3

theorem join_1_0 : (twinPrimeSegment 347865133 347996205).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 347865133 ≤ 347930669)
    (by decide : 347930669 ≤ 347996205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 347865133 347996205).card = 448 := join_1_0

end S165C14
end Sude.GeneratedTwinScan
