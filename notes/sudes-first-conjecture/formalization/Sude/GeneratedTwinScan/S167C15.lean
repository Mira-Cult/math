import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18767)) 352190509 352223277 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 352190509 352223277).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18767 352190509 352223277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18768)) 352223277 352256045 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 352223277 352256045).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18768 352223277 352256045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18769)) 352256045 352288813 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 352256045 352288813).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18769 352256045 352288813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18770)) 352288813 352321581 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 352288813 352321581).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18770 352288813 352321581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 352190509 352256045).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 352190509 ≤ 352223277)
    (by decide : 352223277 ≤ 352256045) block0 block1

theorem join_0_1 : (twinPrimeSegment 352256045 352321581).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 352256045 ≤ 352288813)
    (by decide : 352288813 ≤ 352321581) block2 block3

theorem join_1_0 : (twinPrimeSegment 352190509 352321581).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 352190509 ≤ 352256045)
    (by decide : 352256045 ≤ 352321581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 352190509 352321581).card = 435 := join_1_0

end S167C15
end Sude.GeneratedTwinScan
