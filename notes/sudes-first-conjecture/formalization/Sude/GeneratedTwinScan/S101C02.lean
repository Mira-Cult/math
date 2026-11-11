import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14563)) 212074541 212107309 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 212074541 212107309).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14563 212074541 212107309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14565)) 212107309 212140077 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 212107309 212140077).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14565 212107309 212140077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14566)) 212140077 212172845 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 212140077 212172845).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14566 212140077 212172845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14567)) 212172845 212205613 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 212172845 212205613).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14567 212172845 212205613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 212074541 212140077).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 212074541 ≤ 212107309)
    (by decide : 212107309 ≤ 212140077) block0 block1

theorem join_0_1 : (twinPrimeSegment 212140077 212205613).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 212140077 ≤ 212172845)
    (by decide : 212172845 ≤ 212205613) block2 block3

theorem join_1_0 : (twinPrimeSegment 212074541 212205613).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 212074541 ≤ 212140077)
    (by decide : 212140077 ≤ 212205613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 212074541 212205613).card = 454 := join_1_0

end S101C02
end Sude.GeneratedTwinScan
