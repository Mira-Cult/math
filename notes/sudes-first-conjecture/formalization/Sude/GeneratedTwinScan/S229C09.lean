import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21942)) 481427501 481460269 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 481427501 481460269).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21942 481427501 481460269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21942)) 481460269 481493037 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 481460269 481493037).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21942 481460269 481493037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21943)) 481493037 481525805 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 481493037 481525805).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21943 481493037 481525805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21944)) 481525805 481558573 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 481525805 481558573).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21944 481525805 481558573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 481427501 481493037).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 481427501 ≤ 481460269)
    (by decide : 481460269 ≤ 481493037) block0 block1

theorem join_0_1 : (twinPrimeSegment 481493037 481558573).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 481493037 ≤ 481525805)
    (by decide : 481525805 ≤ 481558573) block2 block3

theorem join_1_0 : (twinPrimeSegment 481427501 481558573).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 481427501 ≤ 481493037)
    (by decide : 481493037 ≤ 481558573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 481427501 481558573).card = 450 := join_1_0

end S229C09
end Sude.GeneratedTwinScan
