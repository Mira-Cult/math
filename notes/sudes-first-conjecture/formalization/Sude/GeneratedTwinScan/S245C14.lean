import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22708)) 515637293 515670061 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 515637293 515670061).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22708 515637293 515670061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22709)) 515670061 515702829 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 515670061 515702829).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22709 515670061 515702829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22709)) 515702829 515735597 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 515702829 515735597).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22709 515702829 515735597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22710)) 515735597 515768365 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 515735597 515768365).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22710 515735597 515768365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 515637293 515702829).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 515637293 ≤ 515670061)
    (by decide : 515670061 ≤ 515702829) block0 block1

theorem join_0_1 : (twinPrimeSegment 515702829 515768365).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 515702829 ≤ 515735597)
    (by decide : 515735597 ≤ 515768365) block2 block3

theorem join_1_0 : (twinPrimeSegment 515637293 515768365).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 515637293 ≤ 515702829)
    (by decide : 515702829 ≤ 515768365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 515637293 515768365).card = 423 := join_1_0

end S245C14
end Sude.GeneratedTwinScan
