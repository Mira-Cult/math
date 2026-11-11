import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18239)) 332660781 332693549 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 332660781 332693549).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18239 332660781 332693549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18240)) 332693549 332726317 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 332693549 332726317).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18240 332693549 332726317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18241)) 332726317 332759085 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 332726317 332759085).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18241 332726317 332759085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18242)) 332759085 332791853 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 332759085 332791853).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18242 332759085 332791853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 332660781 332726317).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 332660781 ≤ 332693549)
    (by decide : 332693549 ≤ 332726317) block0 block1

theorem join_0_1 : (twinPrimeSegment 332726317 332791853).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 332726317 ≤ 332759085)
    (by decide : 332759085 ≤ 332791853) block2 block3

theorem join_1_0 : (twinPrimeSegment 332660781 332791853).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 332660781 ≤ 332726317)
    (by decide : 332726317 ≤ 332791853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 332660781 332791853).card = 478 := join_1_0

end S158C10
end Sude.GeneratedTwinScan
