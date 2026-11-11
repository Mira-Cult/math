import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12574)) 158072877 158105645 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 158072877 158105645).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12574 158072877 158105645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12575)) 158105645 158138413 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 158105645 158138413).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12575 158105645 158138413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12576)) 158138413 158171181 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 158138413 158171181).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12576 158138413 158171181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12577)) 158171181 158203949 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 158171181 158203949).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12577 158171181 158203949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 158072877 158138413).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 158072877 ≤ 158105645)
    (by decide : 158105645 ≤ 158138413) block0 block1

theorem join_0_1 : (twinPrimeSegment 158138413 158203949).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 158138413 ≤ 158171181)
    (by decide : 158171181 ≤ 158203949) block2 block3

theorem join_1_0 : (twinPrimeSegment 158072877 158203949).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 158072877 ≤ 158138413)
    (by decide : 158138413 ≤ 158203949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 158072877 158203949).card = 507 := join_1_0

end S075C06
end Sude.GeneratedTwinScan
