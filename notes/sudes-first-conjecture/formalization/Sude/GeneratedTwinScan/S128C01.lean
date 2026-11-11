import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16389)) 268566573 268599341 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 268566573 268599341).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16389 268566573 268599341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16390)) 268599341 268632109 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 268599341 268632109).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16390 268599341 268632109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16391)) 268632109 268664877 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 268632109 268664877).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16391 268632109 268664877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16391)) 268664877 268697645 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 268664877 268697645).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16391 268664877 268697645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 268566573 268632109).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 268566573 ≤ 268599341)
    (by decide : 268599341 ≤ 268632109) block0 block1

theorem join_0_1 : (twinPrimeSegment 268632109 268697645).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 268632109 ≤ 268664877)
    (by decide : 268664877 ≤ 268697645) block2 block3

theorem join_1_0 : (twinPrimeSegment 268566573 268697645).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 268566573 ≤ 268632109)
    (by decide : 268632109 ≤ 268697645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 268566573 268697645).card = 439 := join_1_0

end S128C01
end Sude.GeneratedTwinScan
