import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20598)) 424280109 424312877 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 424280109 424312877).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20598 424280109 424312877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20599)) 424312877 424345645 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 424312877 424345645).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20599 424312877 424345645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20600)) 424345645 424378413 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 424345645 424378413).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20600 424345645 424378413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20601)) 424378413 424411181 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 424378413 424411181).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20601 424378413 424411181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 424280109 424345645).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 424280109 ≤ 424312877)
    (by decide : 424312877 ≤ 424345645) block0 block1

theorem join_0_1 : (twinPrimeSegment 424345645 424411181).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 424345645 ≤ 424378413)
    (by decide : 424378413 ≤ 424411181) block2 block3

theorem join_1_0 : (twinPrimeSegment 424280109 424411181).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 424280109 ≤ 424345645)
    (by decide : 424345645 ≤ 424411181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 424280109 424411181).card = 485 := join_1_0

end S202C05
end Sude.GeneratedTwinScan
