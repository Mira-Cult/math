import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22335)) 498860077 498892845 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 498860077 498892845).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22335 498860077 498892845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22336)) 498892845 498925613 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 498892845 498925613).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22336 498892845 498925613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22337)) 498925613 498958381 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 498925613 498958381).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22337 498925613 498958381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22338)) 498958381 498991149 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 498958381 498991149).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22338 498958381 498991149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 498860077 498925613).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 498860077 ≤ 498892845)
    (by decide : 498892845 ≤ 498925613) block0 block1

theorem join_0_1 : (twinPrimeSegment 498925613 498991149).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 498925613 ≤ 498958381)
    (by decide : 498958381 ≤ 498991149) block2 block3

theorem join_1_0 : (twinPrimeSegment 498860077 498991149).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 498860077 ≤ 498925613)
    (by decide : 498925613 ≤ 498991149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 498860077 498991149).card = 433 := join_1_0

end S237C14
end Sude.GeneratedTwinScan
