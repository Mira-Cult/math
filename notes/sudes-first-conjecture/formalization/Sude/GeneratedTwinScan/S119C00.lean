import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15798)) 249561133 249593901 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 249561133 249593901).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15798 249561133 249593901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15799)) 249593901 249626669 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 249593901 249626669).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15799 249593901 249626669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15800)) 249626669 249659437 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 249626669 249659437).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15800 249626669 249659437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15801)) 249659437 249692205 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 249659437 249692205).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15801 249659437 249692205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 249561133 249626669).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 249561133 ≤ 249593901)
    (by decide : 249593901 ≤ 249626669) block0 block1

theorem join_0_1 : (twinPrimeSegment 249626669 249692205).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 249626669 ≤ 249659437)
    (by decide : 249659437 ≤ 249692205) block2 block3

theorem join_1_0 : (twinPrimeSegment 249561133 249692205).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 249561133 ≤ 249626669)
    (by decide : 249626669 ≤ 249692205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 249561133 249692205).card = 465 := join_1_0

end S119C00
end Sude.GeneratedTwinScan
