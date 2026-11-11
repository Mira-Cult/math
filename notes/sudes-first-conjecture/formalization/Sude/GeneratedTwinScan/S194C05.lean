import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20187)) 407502893 407535661 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 407502893 407535661).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20187 407502893 407535661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20188)) 407535661 407568429 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 407535661 407568429).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20188 407535661 407568429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20189)) 407568429 407601197 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 407568429 407601197).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20189 407568429 407601197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20189)) 407601197 407633965 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 407601197 407633965).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20189 407601197 407633965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 407502893 407568429).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 407502893 ≤ 407535661)
    (by decide : 407535661 ≤ 407568429) block0 block1

theorem join_0_1 : (twinPrimeSegment 407568429 407633965).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 407568429 ≤ 407601197)
    (by decide : 407601197 ≤ 407633965) block2 block3

theorem join_1_0 : (twinPrimeSegment 407502893 407633965).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 407502893 ≤ 407568429)
    (by decide : 407568429 ≤ 407633965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 407502893 407633965).card = 481 := join_1_0

end S194C05
end Sude.GeneratedTwinScan
