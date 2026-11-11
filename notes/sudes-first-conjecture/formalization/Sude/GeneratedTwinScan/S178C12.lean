import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19362)) 374865965 374898733 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 374865965 374898733).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19362 374865965 374898733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19363)) 374898733 374931501 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 374898733 374931501).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19363 374898733 374931501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19363)) 374931501 374964269 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 374931501 374964269).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19363 374931501 374964269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19364)) 374964269 374997037 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 374964269 374997037).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19364 374964269 374997037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 374865965 374931501).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 374865965 ≤ 374898733)
    (by decide : 374898733 ≤ 374931501) block0 block1

theorem join_0_1 : (twinPrimeSegment 374931501 374997037).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 374931501 ≤ 374964269)
    (by decide : 374964269 ≤ 374997037) block2 block3

theorem join_1_0 : (twinPrimeSegment 374865965 374997037).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 374865965 ≤ 374931501)
    (by decide : 374931501 ≤ 374997037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 374865965 374997037).card = 454 := join_1_0

end S178C12
end Sude.GeneratedTwinScan
