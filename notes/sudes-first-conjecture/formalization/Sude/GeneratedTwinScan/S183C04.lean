import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19604)) 384303149 384335917 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 384303149 384335917).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19604 384303149 384335917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19605)) 384335917 384368685 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 384335917 384368685).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19605 384335917 384368685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19606)) 384368685 384401453 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 384368685 384401453).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19606 384368685 384401453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19606)) 384401453 384434221 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 384401453 384434221).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19606 384401453 384434221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 384303149 384368685).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 384303149 ≤ 384335917)
    (by decide : 384335917 ≤ 384368685) block0 block1

theorem join_0_1 : (twinPrimeSegment 384368685 384434221).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 384368685 ≤ 384401453)
    (by decide : 384401453 ≤ 384434221) block2 block3

theorem join_1_0 : (twinPrimeSegment 384303149 384434221).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 384303149 ≤ 384368685)
    (by decide : 384368685 ≤ 384434221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 384303149 384434221).card = 418 := join_1_0

end S183C04
end Sude.GeneratedTwinScan
