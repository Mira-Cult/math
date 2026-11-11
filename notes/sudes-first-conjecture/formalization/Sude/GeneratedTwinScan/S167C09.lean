import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18746)) 351404077 351436845 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 351404077 351436845).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18746 351404077 351436845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18747)) 351436845 351469613 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 351436845 351469613).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18747 351436845 351469613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18748)) 351469613 351502381 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 351469613 351502381).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18748 351469613 351502381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18749)) 351502381 351535149 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 351502381 351535149).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18749 351502381 351535149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 351404077 351469613).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 351404077 ≤ 351436845)
    (by decide : 351436845 ≤ 351469613) block0 block1

theorem join_0_1 : (twinPrimeSegment 351469613 351535149).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 351469613 ≤ 351502381)
    (by decide : 351502381 ≤ 351535149) block2 block3

theorem join_1_0 : (twinPrimeSegment 351404077 351535149).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 351404077 ≤ 351469613)
    (by decide : 351469613 ≤ 351535149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 351404077 351535149).card = 481 := join_1_0

end S167C09
end Sude.GeneratedTwinScan
