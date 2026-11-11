import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20820)) 433455149 433487917 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 433455149 433487917).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20820 433455149 433487917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20821)) 433487917 433520685 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 433487917 433520685).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20821 433487917 433520685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20821)) 433520685 433553453 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 433520685 433553453).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20821 433520685 433553453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20822)) 433553453 433586221 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 433553453 433586221).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20822 433553453 433586221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 433455149 433520685).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 433455149 ≤ 433487917)
    (by decide : 433487917 ≤ 433520685) block0 block1

theorem join_0_1 : (twinPrimeSegment 433520685 433586221).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 433520685 ≤ 433553453)
    (by decide : 433553453 ≤ 433586221) block2 block3

theorem join_1_0 : (twinPrimeSegment 433455149 433586221).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 433455149 ≤ 433520685)
    (by decide : 433520685 ≤ 433586221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 433455149 433586221).card = 447 := join_1_0

end S206C11
end Sude.GeneratedTwinScan
