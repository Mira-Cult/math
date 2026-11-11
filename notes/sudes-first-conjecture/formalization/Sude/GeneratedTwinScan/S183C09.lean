import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19621)) 384958509 384991277 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 384958509 384991277).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19621 384958509 384991277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19622)) 384991277 385024045 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 384991277 385024045).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19622 384991277 385024045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19622)) 385024045 385056813 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 385024045 385056813).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19622 385024045 385056813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19623)) 385056813 385089581 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 385056813 385089581).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19623 385056813 385089581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 384958509 385024045).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 384958509 ≤ 384991277)
    (by decide : 384991277 ≤ 385024045) block0 block1

theorem join_0_1 : (twinPrimeSegment 385024045 385089581).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 385024045 ≤ 385056813)
    (by decide : 385056813 ≤ 385089581) block2 block3

theorem join_1_0 : (twinPrimeSegment 384958509 385089581).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 384958509 ≤ 385024045)
    (by decide : 385024045 ≤ 385089581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 384958509 385089581).card = 439 := join_1_0

end S183C09
end Sude.GeneratedTwinScan
