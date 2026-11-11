import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20320)) 412876845 412909613 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 412876845 412909613).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20320 412876845 412909613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20320)) 412909613 412942381 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 412909613 412942381).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20320 412909613 412942381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20321)) 412942381 412975149 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 412942381 412975149).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20321 412942381 412975149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20322)) 412975149 413007917 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 412975149 413007917).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20322 412975149 413007917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 412876845 412942381).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 412876845 ≤ 412909613)
    (by decide : 412909613 ≤ 412942381) block0 block1

theorem join_0_1 : (twinPrimeSegment 412942381 413007917).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 412942381 ≤ 412975149)
    (by decide : 412975149 ≤ 413007917) block2 block3

theorem join_1_0 : (twinPrimeSegment 412876845 413007917).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 412876845 ≤ 412942381)
    (by decide : 412942381 ≤ 413007917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 412876845 413007917).card = 441 := join_1_0

end S196C14
end Sude.GeneratedTwinScan
