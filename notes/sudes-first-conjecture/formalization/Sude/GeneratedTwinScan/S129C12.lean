import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16496)) 272105517 272138285 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 272105517 272138285).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16496 272105517 272138285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16497)) 272138285 272171053 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 272138285 272171053).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16497 272138285 272171053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16498)) 272171053 272203821 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 272171053 272203821).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16498 272171053 272203821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16499)) 272203821 272236589 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 272203821 272236589).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16499 272203821 272236589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 272105517 272171053).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 272105517 ≤ 272138285)
    (by decide : 272138285 ≤ 272171053) block0 block1

theorem join_0_1 : (twinPrimeSegment 272171053 272236589).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 272171053 ≤ 272203821)
    (by decide : 272203821 ≤ 272236589) block2 block3

theorem join_1_0 : (twinPrimeSegment 272105517 272236589).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 272105517 ≤ 272171053)
    (by decide : 272171053 ≤ 272236589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 272105517 272236589).card = 447 := join_1_0

end S129C12
end Sude.GeneratedTwinScan
