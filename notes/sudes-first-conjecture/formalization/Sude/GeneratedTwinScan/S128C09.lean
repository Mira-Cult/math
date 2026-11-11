import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16420)) 269615149 269647917 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 269615149 269647917).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16420 269615149 269647917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16421)) 269647917 269680685 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 269647917 269680685).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16421 269647917 269680685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16422)) 269680685 269713453 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 269680685 269713453).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16422 269680685 269713453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16423)) 269713453 269746221 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 269713453 269746221).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16423 269713453 269746221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 269615149 269680685).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 269615149 ≤ 269647917)
    (by decide : 269647917 ≤ 269680685) block0 block1

theorem join_0_1 : (twinPrimeSegment 269680685 269746221).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 269680685 ≤ 269713453)
    (by decide : 269713453 ≤ 269746221) block2 block3

theorem join_1_0 : (twinPrimeSegment 269615149 269746221).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 269615149 ≤ 269680685)
    (by decide : 269680685 ≤ 269746221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 269615149 269746221).card = 490 := join_1_0

end S128C09
end Sude.GeneratedTwinScan
