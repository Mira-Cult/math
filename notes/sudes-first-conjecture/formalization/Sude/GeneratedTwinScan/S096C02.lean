import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14199)) 201588781 201621549 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 201588781 201621549).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14199 201588781 201621549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14200)) 201621549 201654317 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 201621549 201654317).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14200 201621549 201654317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14201)) 201654317 201687085 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 201654317 201687085).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14201 201654317 201687085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14202)) 201687085 201719853 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 201687085 201719853).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14202 201687085 201719853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 201588781 201654317).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 201588781 ≤ 201621549)
    (by decide : 201621549 ≤ 201654317) block0 block1

theorem join_0_1 : (twinPrimeSegment 201654317 201719853).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 201654317 ≤ 201687085)
    (by decide : 201687085 ≤ 201719853) block2 block3

theorem join_1_0 : (twinPrimeSegment 201588781 201719853).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 201588781 ≤ 201654317)
    (by decide : 201654317 ≤ 201719853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 201588781 201719853).card = 467 := join_1_0

end S096C02
end Sude.GeneratedTwinScan
