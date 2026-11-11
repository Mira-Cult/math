import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18927)) 358219821 358252589 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 358219821 358252589).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18927 358219821 358252589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18928)) 358252589 358285357 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 358252589 358285357).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18928 358252589 358285357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18929)) 358285357 358318125 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 358285357 358318125).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18929 358285357 358318125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18930)) 358318125 358350893 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 358318125 358350893).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18930 358318125 358350893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 358219821 358285357).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 358219821 ≤ 358252589)
    (by decide : 358252589 ≤ 358285357) block0 block1

theorem join_0_1 : (twinPrimeSegment 358285357 358350893).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 358285357 ≤ 358318125)
    (by decide : 358318125 ≤ 358350893) block2 block3

theorem join_1_0 : (twinPrimeSegment 358219821 358350893).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 358219821 ≤ 358285357)
    (by decide : 358285357 ≤ 358350893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 358219821 358350893).card = 431 := join_1_0

end S170C13
end Sude.GeneratedTwinScan
