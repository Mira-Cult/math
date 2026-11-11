import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17751)) 315097133 315129901 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 315097133 315129901).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17751 315097133 315129901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17752)) 315129901 315162669 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 315129901 315162669).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17752 315129901 315162669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17753)) 315162669 315195437 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 315162669 315195437).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17753 315162669 315195437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17754)) 315195437 315228205 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 315195437 315228205).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17754 315195437 315228205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 315097133 315162669).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 315097133 ≤ 315129901)
    (by decide : 315129901 ≤ 315162669) block0 block1

theorem join_0_1 : (twinPrimeSegment 315162669 315228205).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 315162669 ≤ 315195437)
    (by decide : 315195437 ≤ 315228205) block2 block3

theorem join_1_0 : (twinPrimeSegment 315097133 315228205).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 315097133 ≤ 315162669)
    (by decide : 315162669 ≤ 315228205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 315097133 315228205).card = 435 := join_1_0

end S150C04
end Sude.GeneratedTwinScan
