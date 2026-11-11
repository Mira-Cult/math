import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17469)) 305135661 305168429 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 305135661 305168429).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17469 305135661 305168429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17470)) 305168429 305201197 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 305168429 305201197).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17470 305168429 305201197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17470)) 305201197 305233965 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 305201197 305233965).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17470 305201197 305233965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17471)) 305233965 305266733 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 305233965 305266733).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17471 305233965 305266733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 305135661 305201197).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 305135661 ≤ 305168429)
    (by decide : 305168429 ≤ 305201197) block0 block1

theorem join_0_1 : (twinPrimeSegment 305201197 305266733).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 305201197 ≤ 305233965)
    (by decide : 305233965 ≤ 305266733) block2 block3

theorem join_1_0 : (twinPrimeSegment 305135661 305266733).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 305135661 ≤ 305201197)
    (by decide : 305201197 ≤ 305266733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 305135661 305266733).card = 441 := join_1_0

end S145C08
end Sude.GeneratedTwinScan
