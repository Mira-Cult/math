import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14572)) 212336685 212369453 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 212336685 212369453).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14572 212336685 212369453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14574)) 212369453 212402221 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 212369453 212402221).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14574 212369453 212402221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14575)) 212402221 212434989 = 85 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 212402221 212434989).card = 85 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14575 212402221 212434989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14576)) 212434989 212467757 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 212434989 212467757).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14576 212434989 212467757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 212336685 212402221).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 212336685 ≤ 212369453)
    (by decide : 212369453 ≤ 212402221) block0 block1

theorem join_0_1 : (twinPrimeSegment 212402221 212467757).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 212402221 ≤ 212434989)
    (by decide : 212434989 ≤ 212467757) block2 block3

theorem join_1_0 : (twinPrimeSegment 212336685 212467757).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 212336685 ≤ 212402221)
    (by decide : 212402221 ≤ 212467757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 212336685 212467757).card = 428 := join_1_0

end S101C04
end Sude.GeneratedTwinScan
