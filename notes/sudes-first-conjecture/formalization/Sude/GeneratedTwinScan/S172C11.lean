import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19031)) 362151981 362184749 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 362151981 362184749).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19031 362151981 362184749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19032)) 362184749 362217517 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 362184749 362217517).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19032 362184749 362217517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19032)) 362217517 362250285 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 362217517 362250285).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19032 362217517 362250285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19033)) 362250285 362283053 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 362250285 362283053).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19033 362250285 362283053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 362151981 362217517).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 362151981 ≤ 362184749)
    (by decide : 362184749 ≤ 362217517) block0 block1

theorem join_0_1 : (twinPrimeSegment 362217517 362283053).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 362217517 ≤ 362250285)
    (by decide : 362250285 ≤ 362283053) block2 block3

theorem join_1_0 : (twinPrimeSegment 362151981 362283053).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 362151981 ≤ 362217517)
    (by decide : 362217517 ≤ 362283053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 362151981 362283053).card = 429 := join_1_0

end S172C11
end Sude.GeneratedTwinScan
