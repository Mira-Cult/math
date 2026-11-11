import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13796)) 190316589 190349357 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 190316589 190349357).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13796 190316589 190349357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13797)) 190349357 190382125 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 190349357 190382125).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13797 190349357 190382125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13799)) 190382125 190414893 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 190382125 190414893).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13799 190382125 190414893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13800)) 190414893 190447661 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 190414893 190447661).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13800 190414893 190447661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 190316589 190382125).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 190316589 ≤ 190349357)
    (by decide : 190349357 ≤ 190382125) block0 block1

theorem join_0_1 : (twinPrimeSegment 190382125 190447661).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 190382125 ≤ 190414893)
    (by decide : 190414893 ≤ 190447661) block2 block3

theorem join_1_0 : (twinPrimeSegment 190316589 190447661).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 190316589 ≤ 190382125)
    (by decide : 190382125 ≤ 190447661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 190316589 190447661).card = 467 := join_1_0

end S090C12
end Sude.GeneratedTwinScan
