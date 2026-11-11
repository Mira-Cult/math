import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18941)) 358744109 358776877 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 358744109 358776877).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18941 358744109 358776877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18942)) 358776877 358809645 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 358776877 358809645).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18942 358776877 358809645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18943)) 358809645 358842413 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 358809645 358842413).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18943 358809645 358842413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18944)) 358842413 358875181 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 358842413 358875181).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18944 358842413 358875181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 358744109 358809645).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 358744109 ≤ 358776877)
    (by decide : 358776877 ≤ 358809645) block0 block1

theorem join_0_1 : (twinPrimeSegment 358809645 358875181).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 358809645 ≤ 358842413)
    (by decide : 358842413 ≤ 358875181) block2 block3

theorem join_1_0 : (twinPrimeSegment 358744109 358875181).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 358744109 ≤ 358809645)
    (by decide : 358809645 ≤ 358875181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 358744109 358875181).card = 485 := join_1_0

end S171C01
end Sude.GeneratedTwinScan
