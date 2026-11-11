import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19560)) 382599213 382631981 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 382599213 382631981).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19560 382599213 382631981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19561)) 382631981 382664749 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 382631981 382664749).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19561 382631981 382664749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19562)) 382664749 382697517 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 382664749 382697517).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19562 382664749 382697517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19563)) 382697517 382730285 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 382697517 382730285).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19563 382697517 382730285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 382599213 382664749).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 382599213 ≤ 382631981)
    (by decide : 382631981 ≤ 382664749) block0 block1

theorem join_0_1 : (twinPrimeSegment 382664749 382730285).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 382664749 ≤ 382697517)
    (by decide : 382697517 ≤ 382730285) block2 block3

theorem join_1_0 : (twinPrimeSegment 382599213 382730285).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 382599213 ≤ 382664749)
    (by decide : 382664749 ≤ 382730285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 382599213 382730285).card = 463 := join_1_0

end S182C07
end Sude.GeneratedTwinScan
