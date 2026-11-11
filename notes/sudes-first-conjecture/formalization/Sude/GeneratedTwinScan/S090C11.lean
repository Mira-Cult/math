import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13791)) 190185517 190218285 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 190185517 190218285).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13791 190185517 190218285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13793)) 190218285 190251053 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 190218285 190251053).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13793 190218285 190251053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13794)) 190251053 190283821 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 190251053 190283821).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13794 190251053 190283821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13795)) 190283821 190316589 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 190283821 190316589).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13795 190283821 190316589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 190185517 190251053).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 190185517 ≤ 190218285)
    (by decide : 190218285 ≤ 190251053) block0 block1

theorem join_0_1 : (twinPrimeSegment 190251053 190316589).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 190251053 ≤ 190283821)
    (by decide : 190283821 ≤ 190316589) block2 block3

theorem join_1_0 : (twinPrimeSegment 190185517 190316589).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 190185517 ≤ 190251053)
    (by decide : 190251053 ≤ 190316589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 190185517 190316589).card = 464 := join_1_0

end S090C11
end Sude.GeneratedTwinScan
