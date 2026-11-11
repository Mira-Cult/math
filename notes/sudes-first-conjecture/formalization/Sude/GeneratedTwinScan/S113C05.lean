import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15416)) 237633581 237666349 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 237633581 237666349).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15416 237633581 237666349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15417)) 237666349 237699117 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 237666349 237699117).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15417 237666349 237699117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15418)) 237699117 237731885 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 237699117 237731885).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15418 237699117 237731885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15419)) 237731885 237764653 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 237731885 237764653).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15419 237731885 237764653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 237633581 237699117).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 237633581 ≤ 237666349)
    (by decide : 237666349 ≤ 237699117) block0 block1

theorem join_0_1 : (twinPrimeSegment 237699117 237764653).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 237699117 ≤ 237731885)
    (by decide : 237731885 ≤ 237764653) block2 block3

theorem join_1_0 : (twinPrimeSegment 237633581 237764653).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 237633581 ≤ 237699117)
    (by decide : 237699117 ≤ 237764653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 237633581 237764653).card = 453 := join_1_0

end S113C05
end Sude.GeneratedTwinScan
