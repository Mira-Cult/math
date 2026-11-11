import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13337)) 177864749 177897517 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 177864749 177897517).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13337 177864749 177897517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13339)) 177897517 177930285 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 177897517 177930285).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13339 177897517 177930285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13340)) 177930285 177963053 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 177930285 177963053).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13340 177930285 177963053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13341)) 177963053 177995821 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 177963053 177995821).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13341 177963053 177995821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 177864749 177930285).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 177864749 ≤ 177897517)
    (by decide : 177897517 ≤ 177930285) block0 block1

theorem join_0_1 : (twinPrimeSegment 177930285 177995821).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 177930285 ≤ 177963053)
    (by decide : 177963053 ≤ 177995821) block2 block3

theorem join_1_0 : (twinPrimeSegment 177864749 177995821).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 177864749 ≤ 177930285)
    (by decide : 177930285 ≤ 177995821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 177864749 177995821).card = 480 := join_1_0

end S084C13
end Sude.GeneratedTwinScan
