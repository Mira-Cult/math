import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16662)) 277610541 277643309 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 277610541 277643309).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16662 277610541 277643309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16663)) 277643309 277676077 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 277643309 277676077).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16663 277643309 277676077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16664)) 277676077 277708845 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 277676077 277708845).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16664 277676077 277708845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16665)) 277708845 277741613 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 277708845 277741613).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16665 277708845 277741613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 277610541 277676077).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 277610541 ≤ 277643309)
    (by decide : 277643309 ≤ 277676077) block0 block1

theorem join_0_1 : (twinPrimeSegment 277676077 277741613).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 277676077 ≤ 277708845)
    (by decide : 277708845 ≤ 277741613) block2 block3

theorem join_1_0 : (twinPrimeSegment 277610541 277741613).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 277610541 ≤ 277676077)
    (by decide : 277676077 ≤ 277741613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 277610541 277741613).card = 469 := join_1_0

end S132C06
end Sude.GeneratedTwinScan
