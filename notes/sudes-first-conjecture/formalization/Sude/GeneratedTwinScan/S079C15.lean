import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12948)) 167641133 167673901 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 167641133 167673901).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12948 167641133 167673901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12950)) 167673901 167706669 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 167673901 167706669).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12950 167673901 167706669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12951)) 167706669 167739437 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 167706669 167739437).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12951 167706669 167739437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12952)) 167739437 167772205 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 167739437 167772205).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12952 167739437 167772205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 167641133 167706669).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 167641133 ≤ 167673901)
    (by decide : 167673901 ≤ 167706669) block0 block1

theorem join_0_1 : (twinPrimeSegment 167706669 167772205).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 167706669 ≤ 167739437)
    (by decide : 167739437 ≤ 167772205) block2 block3

theorem join_1_0 : (twinPrimeSegment 167641133 167772205).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 167641133 ≤ 167706669)
    (by decide : 167706669 ≤ 167772205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 167641133 167772205).card = 491 := join_1_0

end S079C15
end Sude.GeneratedTwinScan
