import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13391)) 179306541 179339309 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 179306541 179339309).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13391 179306541 179339309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13392)) 179339309 179372077 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 179339309 179372077).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13392 179339309 179372077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13394)) 179372077 179404845 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 179372077 179404845).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13394 179372077 179404845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13395)) 179404845 179437613 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 179404845 179437613).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13395 179404845 179437613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 179306541 179372077).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 179306541 ≤ 179339309)
    (by decide : 179339309 ≤ 179372077) block0 block1

theorem join_0_1 : (twinPrimeSegment 179372077 179437613).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 179372077 ≤ 179404845)
    (by decide : 179404845 ≤ 179437613) block2 block3

theorem join_1_0 : (twinPrimeSegment 179306541 179437613).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 179306541 ≤ 179372077)
    (by decide : 179372077 ≤ 179437613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 179306541 179437613).card = 498 := join_1_0

end S085C08
end Sude.GeneratedTwinScan
