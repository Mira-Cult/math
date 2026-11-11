import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22493)) 505937965 505970733 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 505937965 505970733).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22493 505937965 505970733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22494)) 505970733 506003501 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 505970733 506003501).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22494 505970733 506003501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22495)) 506003501 506036269 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 506003501 506036269).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22495 506003501 506036269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22495)) 506036269 506069037 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 506036269 506069037).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22495 506036269 506069037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 505937965 506003501).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 505937965 ≤ 505970733)
    (by decide : 505970733 ≤ 506003501) block0 block1

theorem join_0_1 : (twinPrimeSegment 506003501 506069037).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 506003501 ≤ 506036269)
    (by decide : 506036269 ≤ 506069037) block2 block3

theorem join_1_0 : (twinPrimeSegment 505937965 506069037).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 505937965 ≤ 506003501)
    (by decide : 506003501 ≤ 506069037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 505937965 506069037).card = 438 := join_1_0

end S241C04
end Sude.GeneratedTwinScan
