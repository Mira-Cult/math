import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19250)) 370540589 370573357 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 370540589 370573357).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19250 370540589 370573357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19251)) 370573357 370606125 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 370573357 370606125).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19251 370573357 370606125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19251)) 370606125 370638893 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 370606125 370638893).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19251 370606125 370638893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19252)) 370638893 370671661 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 370638893 370671661).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19252 370638893 370671661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 370540589 370606125).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 370540589 ≤ 370573357)
    (by decide : 370573357 ≤ 370606125) block0 block1

theorem join_0_1 : (twinPrimeSegment 370606125 370671661).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 370606125 ≤ 370638893)
    (by decide : 370638893 ≤ 370671661) block2 block3

theorem join_1_0 : (twinPrimeSegment 370540589 370671661).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 370540589 ≤ 370606125)
    (by decide : 370606125 ≤ 370671661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 370540589 370671661).card = 460 := join_1_0

end S176C11
end Sude.GeneratedTwinScan
