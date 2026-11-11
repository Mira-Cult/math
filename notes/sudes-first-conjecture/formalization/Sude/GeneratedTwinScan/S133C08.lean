import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16733)) 279969837 280002605 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 279969837 280002605).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16733 279969837 280002605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16734)) 280002605 280035373 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 280002605 280035373).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16734 280002605 280035373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16735)) 280035373 280068141 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 280035373 280068141).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16735 280035373 280068141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16736)) 280068141 280100909 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 280068141 280100909).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16736 280068141 280100909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 279969837 280035373).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 279969837 ≤ 280002605)
    (by decide : 280002605 ≤ 280035373) block0 block1

theorem join_0_1 : (twinPrimeSegment 280035373 280100909).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 280035373 ≤ 280068141)
    (by decide : 280068141 ≤ 280100909) block2 block3

theorem join_1_0 : (twinPrimeSegment 279969837 280100909).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 279969837 ≤ 280035373)
    (by decide : 280035373 ≤ 280100909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 279969837 280100909).card = 466 := join_1_0

end S133C08
end Sude.GeneratedTwinScan
