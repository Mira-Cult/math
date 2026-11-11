import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17435)) 303956013 303988781 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 303956013 303988781).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17435 303956013 303988781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17436)) 303988781 304021549 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 303988781 304021549).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17436 303988781 304021549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17437)) 304021549 304054317 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 304021549 304054317).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17437 304021549 304054317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17438)) 304054317 304087085 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 304054317 304087085).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17438 304054317 304087085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 303956013 304021549).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 303956013 ≤ 303988781)
    (by decide : 303988781 ≤ 304021549) block0 block1

theorem join_0_1 : (twinPrimeSegment 304021549 304087085).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 304021549 ≤ 304054317)
    (by decide : 304054317 ≤ 304087085) block2 block3

theorem join_1_0 : (twinPrimeSegment 303956013 304087085).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 303956013 ≤ 304021549)
    (by decide : 304021549 ≤ 304087085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 303956013 304087085).card = 440 := join_1_0

end S144C15
end Sude.GeneratedTwinScan
