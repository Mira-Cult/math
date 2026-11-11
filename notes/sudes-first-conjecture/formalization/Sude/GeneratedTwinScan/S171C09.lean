import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18969)) 359792685 359825453 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 359792685 359825453).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18969 359792685 359825453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18969)) 359825453 359858221 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 359825453 359858221).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18969 359825453 359858221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18970)) 359858221 359890989 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 359858221 359890989).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18970 359858221 359890989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18971)) 359890989 359923757 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 359890989 359923757).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18971 359890989 359923757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 359792685 359858221).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 359792685 ≤ 359825453)
    (by decide : 359825453 ≤ 359858221) block0 block1

theorem join_0_1 : (twinPrimeSegment 359858221 359923757).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 359858221 ≤ 359890989)
    (by decide : 359890989 ≤ 359923757) block2 block3

theorem join_1_0 : (twinPrimeSegment 359792685 359923757).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 359792685 ≤ 359858221)
    (by decide : 359858221 ≤ 359923757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 359792685 359923757).card = 443 := join_1_0

end S171C09
end Sude.GeneratedTwinScan
