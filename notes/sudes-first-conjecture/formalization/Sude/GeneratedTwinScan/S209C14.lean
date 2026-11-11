import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20980)) 440139821 440172589 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 440139821 440172589).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20980 440139821 440172589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20981)) 440172589 440205357 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 440172589 440205357).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20981 440172589 440205357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20981)) 440205357 440238125 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 440205357 440238125).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20981 440205357 440238125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20982)) 440238125 440270893 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 440238125 440270893).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20982 440238125 440270893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 440139821 440205357).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 440139821 ≤ 440172589)
    (by decide : 440172589 ≤ 440205357) block0 block1

theorem join_0_1 : (twinPrimeSegment 440205357 440270893).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 440205357 ≤ 440238125)
    (by decide : 440238125 ≤ 440270893) block2 block3

theorem join_1_0 : (twinPrimeSegment 440139821 440270893).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 440139821 ≤ 440205357)
    (by decide : 440205357 ≤ 440270893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 440139821 440270893).card = 461 := join_1_0

end S209C14
end Sude.GeneratedTwinScan
