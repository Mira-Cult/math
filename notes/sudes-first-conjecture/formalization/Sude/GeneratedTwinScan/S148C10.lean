import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17655)) 311689261 311722029 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 311689261 311722029).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17655 311689261 311722029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17656)) 311722029 311754797 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 311722029 311754797).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17656 311722029 311754797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17657)) 311754797 311787565 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 311754797 311787565).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17657 311754797 311787565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17658)) 311787565 311820333 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 311787565 311820333).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17658 311787565 311820333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 311689261 311754797).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 311689261 ≤ 311722029)
    (by decide : 311722029 ≤ 311754797) block0 block1

theorem join_0_1 : (twinPrimeSegment 311754797 311820333).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 311754797 ≤ 311787565)
    (by decide : 311787565 ≤ 311820333) block2 block3

theorem join_1_0 : (twinPrimeSegment 311689261 311820333).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 311689261 ≤ 311754797)
    (by decide : 311754797 ≤ 311820333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 311689261 311820333).card = 454 := join_1_0

end S148C10
end Sude.GeneratedTwinScan
