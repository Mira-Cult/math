import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12765)) 162922541 162955309 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 162922541 162955309).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12765 162922541 162955309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12766)) 162955309 162988077 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 162955309 162988077).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12766 162955309 162988077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12767)) 162988077 163020845 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 162988077 163020845).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12767 162988077 163020845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12769)) 163020845 163053613 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 163020845 163053613).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12769 163020845 163053613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 162922541 162988077).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 162922541 ≤ 162955309)
    (by decide : 162955309 ≤ 162988077) block0 block1

theorem join_0_1 : (twinPrimeSegment 162988077 163053613).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 162988077 ≤ 163020845)
    (by decide : 163020845 ≤ 163053613) block2 block3

theorem join_1_0 : (twinPrimeSegment 162922541 163053613).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 162922541 ≤ 162988077)
    (by decide : 162988077 ≤ 163053613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 162922541 163053613).card = 475 := join_1_0

end S077C11
end Sude.GeneratedTwinScan
