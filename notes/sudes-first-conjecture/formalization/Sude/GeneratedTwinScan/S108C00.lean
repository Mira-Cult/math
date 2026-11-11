import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15050)) 226492461 226525229 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 226492461 226525229).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15050 226492461 226525229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15051)) 226525229 226557997 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 226525229 226557997).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15051 226525229 226557997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15052)) 226557997 226590765 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 226557997 226590765).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15052 226557997 226590765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15054)) 226590765 226623533 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 226590765 226623533).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15054 226590765 226623533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 226492461 226557997).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 226492461 ≤ 226525229)
    (by decide : 226525229 ≤ 226557997) block0 block1

theorem join_0_1 : (twinPrimeSegment 226557997 226623533).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 226557997 ≤ 226590765)
    (by decide : 226590765 ≤ 226623533) block2 block3

theorem join_1_0 : (twinPrimeSegment 226492461 226623533).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 226492461 ≤ 226557997)
    (by decide : 226557997 ≤ 226623533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 226492461 226623533).card = 432 := join_1_0

end S108C00
end Sude.GeneratedTwinScan
