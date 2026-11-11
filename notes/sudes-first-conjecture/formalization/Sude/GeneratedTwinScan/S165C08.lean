import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18630)) 347078701 347111469 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 347078701 347111469).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18630 347078701 347111469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18631)) 347111469 347144237 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 347111469 347144237).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18631 347111469 347144237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18632)) 347144237 347177005 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 347144237 347177005).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18632 347144237 347177005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18633)) 347177005 347209773 = 90 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 347177005 347209773).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18633 347177005 347209773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 347078701 347144237).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 347078701 ≤ 347111469)
    (by decide : 347111469 ≤ 347144237) block0 block1

theorem join_0_1 : (twinPrimeSegment 347144237 347209773).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 347144237 ≤ 347177005)
    (by decide : 347177005 ≤ 347209773) block2 block3

theorem join_1_0 : (twinPrimeSegment 347078701 347209773).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 347078701 ≤ 347144237)
    (by decide : 347144237 ≤ 347209773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 347078701 347209773).card = 427 := join_1_0

end S165C08
end Sude.GeneratedTwinScan
