import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18535)) 343539757 343572525 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 343539757 343572525).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18535 343539757 343572525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18536)) 343572525 343605293 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 343572525 343605293).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18536 343572525 343605293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18537)) 343605293 343638061 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 343605293 343638061).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18537 343605293 343638061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18538)) 343638061 343670829 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 343638061 343670829).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18538 343638061 343670829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 343539757 343605293).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 343539757 ≤ 343572525)
    (by decide : 343572525 ≤ 343605293) block0 block1

theorem join_0_1 : (twinPrimeSegment 343605293 343670829).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 343605293 ≤ 343638061)
    (by decide : 343638061 ≤ 343670829) block2 block3

theorem join_1_0 : (twinPrimeSegment 343539757 343670829).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 343539757 ≤ 343605293)
    (by decide : 343605293 ≤ 343670829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 343539757 343670829).card = 425 := join_1_0

end S163C13
end Sude.GeneratedTwinScan
