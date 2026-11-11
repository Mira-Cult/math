import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14595)) 212992045 213024813 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 212992045 213024813).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14595 212992045 213024813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14596)) 213024813 213057581 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 213024813 213057581).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14596 213024813 213057581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14597)) 213057581 213090349 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 213057581 213090349).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14597 213057581 213090349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14598)) 213090349 213123117 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 213090349 213123117).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14598 213090349 213123117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 212992045 213057581).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 212992045 ≤ 213024813)
    (by decide : 213024813 ≤ 213057581) block0 block1

theorem join_0_1 : (twinPrimeSegment 213057581 213123117).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 213057581 ≤ 213090349)
    (by decide : 213090349 ≤ 213123117) block2 block3

theorem join_1_0 : (twinPrimeSegment 212992045 213123117).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 212992045 ≤ 213057581)
    (by decide : 213057581 ≤ 213123117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 212992045 213123117).card = 480 := join_1_0

end S101C09
end Sude.GeneratedTwinScan
