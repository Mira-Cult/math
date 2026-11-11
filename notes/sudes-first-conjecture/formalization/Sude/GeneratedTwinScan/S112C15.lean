import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15390)) 236847149 236879917 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 236847149 236879917).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15390 236847149 236879917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15391)) 236879917 236912685 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 236879917 236912685).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15391 236879917 236912685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15393)) 236912685 236945453 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 236912685 236945453).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15393 236912685 236945453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15394)) 236945453 236978221 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 236945453 236978221).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15394 236945453 236978221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 236847149 236912685).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 236847149 ≤ 236879917)
    (by decide : 236879917 ≤ 236912685) block0 block1

theorem join_0_1 : (twinPrimeSegment 236912685 236978221).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 236912685 ≤ 236945453)
    (by decide : 236945453 ≤ 236978221) block2 block3

theorem join_1_0 : (twinPrimeSegment 236847149 236978221).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 236847149 ≤ 236912685)
    (by decide : 236912685 ≤ 236978221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 236847149 236978221).card = 465 := join_1_0

end S112C15
end Sude.GeneratedTwinScan
