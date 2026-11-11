import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17412)) 303169581 303202349 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 303169581 303202349).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17412 303169581 303202349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17413)) 303202349 303235117 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 303202349 303235117).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17413 303202349 303235117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17414)) 303235117 303267885 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 303235117 303267885).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17414 303235117 303267885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17415)) 303267885 303300653 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 303267885 303300653).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17415 303267885 303300653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 303169581 303235117).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 303169581 ≤ 303202349)
    (by decide : 303202349 ≤ 303235117) block0 block1

theorem join_0_1 : (twinPrimeSegment 303235117 303300653).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 303235117 ≤ 303267885)
    (by decide : 303267885 ≤ 303300653) block2 block3

theorem join_1_0 : (twinPrimeSegment 303169581 303300653).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 303169581 ≤ 303235117)
    (by decide : 303235117 ≤ 303300653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 303169581 303300653).card = 457 := join_1_0

end S144C09
end Sude.GeneratedTwinScan
