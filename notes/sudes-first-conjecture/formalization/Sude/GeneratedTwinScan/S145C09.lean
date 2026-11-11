import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17472)) 305266733 305299501 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 305266733 305299501).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17472 305266733 305299501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17473)) 305299501 305332269 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 305299501 305332269).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17473 305299501 305332269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17474)) 305332269 305365037 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 305332269 305365037).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17474 305332269 305365037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17475)) 305365037 305397805 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 305365037 305397805).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17475 305365037 305397805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 305266733 305332269).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 305266733 ≤ 305299501)
    (by decide : 305299501 ≤ 305332269) block0 block1

theorem join_0_1 : (twinPrimeSegment 305332269 305397805).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 305332269 ≤ 305365037)
    (by decide : 305365037 ≤ 305397805) block2 block3

theorem join_1_0 : (twinPrimeSegment 305266733 305397805).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 305266733 ≤ 305332269)
    (by decide : 305332269 ≤ 305397805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 305266733 305397805).card = 455 := join_1_0

end S145C09
end Sude.GeneratedTwinScan
