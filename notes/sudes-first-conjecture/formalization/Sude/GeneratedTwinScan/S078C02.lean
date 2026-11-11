import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12801)) 163840045 163872813 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 163840045 163872813).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12801 163840045 163872813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12802)) 163872813 163905581 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 163872813 163905581).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12802 163872813 163905581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12803)) 163905581 163938349 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 163905581 163938349).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12803 163905581 163938349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12805)) 163938349 163971117 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 163938349 163971117).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12805 163938349 163971117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 163840045 163905581).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 163840045 ≤ 163872813)
    (by decide : 163872813 ≤ 163905581) block0 block1

theorem join_0_1 : (twinPrimeSegment 163905581 163971117).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 163905581 ≤ 163938349)
    (by decide : 163938349 ≤ 163971117) block2 block3

theorem join_1_0 : (twinPrimeSegment 163840045 163971117).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 163840045 ≤ 163905581)
    (by decide : 163905581 ≤ 163971117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 163840045 163971117).card = 481 := join_1_0

end S078C02
end Sude.GeneratedTwinScan
