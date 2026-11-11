import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22403)) 501874733 501907501 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 501874733 501907501).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22403 501874733 501907501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22404)) 501907501 501940269 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 501907501 501940269).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22404 501907501 501940269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22404)) 501940269 501973037 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 501940269 501973037).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22404 501940269 501973037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22405)) 501973037 502005805 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 501973037 502005805).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22405 501973037 502005805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 501874733 501940269).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 501874733 ≤ 501907501)
    (by decide : 501907501 ≤ 501940269) block0 block1

theorem join_0_1 : (twinPrimeSegment 501940269 502005805).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 501940269 ≤ 501973037)
    (by decide : 501973037 ≤ 502005805) block2 block3

theorem join_1_0 : (twinPrimeSegment 501874733 502005805).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 501874733 ≤ 501940269)
    (by decide : 501940269 ≤ 502005805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 501874733 502005805).card = 432 := join_1_0

end S239C05
end Sude.GeneratedTwinScan
