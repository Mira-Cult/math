import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21132)) 446562349 446595117 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 446562349 446595117).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21132 446562349 446595117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21133)) 446595117 446627885 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 446595117 446627885).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21133 446595117 446627885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21134)) 446627885 446660653 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 446627885 446660653).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21134 446627885 446660653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21135)) 446660653 446693421 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 446660653 446693421).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21135 446660653 446693421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 446562349 446627885).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 446562349 ≤ 446595117)
    (by decide : 446595117 ≤ 446627885) block0 block1

theorem join_0_1 : (twinPrimeSegment 446627885 446693421).card = 194 := by
  simpa using combineTwinPrimeSegments (by decide : 446627885 ≤ 446660653)
    (by decide : 446660653 ≤ 446693421) block2 block3

theorem join_1_0 : (twinPrimeSegment 446562349 446693421).card = 410 := by
  simpa using combineTwinPrimeSegments (by decide : 446562349 ≤ 446627885)
    (by decide : 446627885 ≤ 446693421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 446562349 446693421).card = 410 := join_1_0

end S212C15
end Sude.GeneratedTwinScan
