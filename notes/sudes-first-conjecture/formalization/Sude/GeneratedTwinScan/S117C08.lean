import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15698)) 246415405 246448173 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 246415405 246448173).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15698 246415405 246448173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15699)) 246448173 246480941 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 246448173 246480941).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15699 246448173 246480941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15700)) 246480941 246513709 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 246480941 246513709).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15700 246480941 246513709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15701)) 246513709 246546477 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 246513709 246546477).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15701 246513709 246546477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 246415405 246480941).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 246415405 ≤ 246448173)
    (by decide : 246448173 ≤ 246480941) block0 block1

theorem join_0_1 : (twinPrimeSegment 246480941 246546477).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 246480941 ≤ 246513709)
    (by decide : 246513709 ≤ 246546477) block2 block3

theorem join_1_0 : (twinPrimeSegment 246415405 246546477).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 246415405 ≤ 246480941)
    (by decide : 246480941 ≤ 246546477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 246415405 246546477).card = 501 := join_1_0

end S117C08
end Sude.GeneratedTwinScan
