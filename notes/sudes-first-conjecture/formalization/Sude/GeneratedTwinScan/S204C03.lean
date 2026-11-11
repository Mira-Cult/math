import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20694)) 428212269 428245037 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 428212269 428245037).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20694 428212269 428245037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20694)) 428245037 428277805 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 428245037 428277805).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20694 428245037 428277805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20695)) 428277805 428310573 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 428277805 428310573).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20695 428277805 428310573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20696)) 428310573 428343341 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 428310573 428343341).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20696 428310573 428343341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 428212269 428277805).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 428212269 ≤ 428245037)
    (by decide : 428245037 ≤ 428277805) block0 block1

theorem join_0_1 : (twinPrimeSegment 428277805 428343341).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 428277805 ≤ 428310573)
    (by decide : 428310573 ≤ 428343341) block2 block3

theorem join_1_0 : (twinPrimeSegment 428212269 428343341).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 428212269 ≤ 428277805)
    (by decide : 428277805 ≤ 428343341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 428212269 428343341).card = 441 := join_1_0

end S204C03
end Sude.GeneratedTwinScan
