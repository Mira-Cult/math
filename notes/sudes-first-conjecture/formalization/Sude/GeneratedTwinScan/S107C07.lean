import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15011)) 225312813 225345581 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 225312813 225345581).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15011 225312813 225345581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15012)) 225345581 225378349 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 225345581 225378349).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15012 225345581 225378349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15013)) 225378349 225411117 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 225378349 225411117).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15013 225378349 225411117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15014)) 225411117 225443885 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 225411117 225443885).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15014 225411117 225443885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 225312813 225378349).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 225312813 ≤ 225345581)
    (by decide : 225345581 ≤ 225378349) block0 block1

theorem join_0_1 : (twinPrimeSegment 225378349 225443885).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 225378349 ≤ 225411117)
    (by decide : 225411117 ≤ 225443885) block2 block3

theorem join_1_0 : (twinPrimeSegment 225312813 225443885).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 225312813 ≤ 225378349)
    (by decide : 225378349 ≤ 225443885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 225312813 225443885).card = 426 := join_1_0

end S107C07
end Sude.GeneratedTwinScan
