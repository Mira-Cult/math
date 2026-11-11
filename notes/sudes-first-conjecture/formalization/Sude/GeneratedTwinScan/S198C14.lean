import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20423)) 417071149 417103917 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 417071149 417103917).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20423 417071149 417103917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20423)) 417103917 417136685 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 417103917 417136685).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20423 417103917 417136685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20424)) 417136685 417169453 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 417136685 417169453).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20424 417136685 417169453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20425)) 417169453 417202221 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 417169453 417202221).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20425 417169453 417202221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 417071149 417136685).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 417071149 ≤ 417103917)
    (by decide : 417103917 ≤ 417136685) block0 block1

theorem join_0_1 : (twinPrimeSegment 417136685 417202221).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 417136685 ≤ 417169453)
    (by decide : 417169453 ≤ 417202221) block2 block3

theorem join_1_0 : (twinPrimeSegment 417071149 417202221).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 417071149 ≤ 417136685)
    (by decide : 417136685 ≤ 417202221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 417071149 417202221).card = 466 := join_1_0

end S198C14
end Sude.GeneratedTwinScan
