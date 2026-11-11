import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17108)) 292683821 292716589 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 292683821 292716589).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17108 292683821 292716589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17109)) 292716589 292749357 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 292716589 292749357).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17109 292716589 292749357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17110)) 292749357 292782125 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 292749357 292782125).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17110 292749357 292782125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17111)) 292782125 292814893 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 292782125 292814893).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17111 292782125 292814893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 292683821 292749357).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 292683821 ≤ 292716589)
    (by decide : 292716589 ≤ 292749357) block0 block1

theorem join_0_1 : (twinPrimeSegment 292749357 292814893).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 292749357 ≤ 292782125)
    (by decide : 292782125 ≤ 292814893) block2 block3

theorem join_1_0 : (twinPrimeSegment 292683821 292814893).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 292683821 ≤ 292749357)
    (by decide : 292749357 ≤ 292814893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 292683821 292814893).card = 494 := join_1_0

end S139C09
end Sude.GeneratedTwinScan
