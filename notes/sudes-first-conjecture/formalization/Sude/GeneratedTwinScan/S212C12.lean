import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21123)) 446169133 446201901 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 446169133 446201901).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21123 446169133 446201901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21124)) 446201901 446234669 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 446201901 446234669).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21124 446201901 446234669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21125)) 446234669 446267437 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 446234669 446267437).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21125 446234669 446267437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21125)) 446267437 446300205 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 446267437 446300205).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21125 446267437 446300205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 446169133 446234669).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 446169133 ≤ 446201901)
    (by decide : 446201901 ≤ 446234669) block0 block1

theorem join_0_1 : (twinPrimeSegment 446234669 446300205).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 446234669 ≤ 446267437)
    (by decide : 446267437 ≤ 446300205) block2 block3

theorem join_1_0 : (twinPrimeSegment 446169133 446300205).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 446169133 ≤ 446234669)
    (by decide : 446234669 ≤ 446300205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 446169133 446300205).card = 430 := join_1_0

end S212C12
end Sude.GeneratedTwinScan
