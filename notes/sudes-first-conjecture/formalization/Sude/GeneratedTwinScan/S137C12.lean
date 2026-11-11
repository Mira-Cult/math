import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16997)) 288882733 288915501 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 288882733 288915501).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16997 288882733 288915501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16998)) 288915501 288948269 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 288915501 288948269).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16998 288915501 288948269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16999)) 288948269 288981037 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 288948269 288981037).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16999 288948269 288981037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17000)) 288981037 289013805 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 288981037 289013805).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17000 288981037 289013805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 288882733 288948269).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 288882733 ≤ 288915501)
    (by decide : 288915501 ≤ 288948269) block0 block1

theorem join_0_1 : (twinPrimeSegment 288948269 289013805).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 288948269 ≤ 288981037)
    (by decide : 288981037 ≤ 289013805) block2 block3

theorem join_1_0 : (twinPrimeSegment 288882733 289013805).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 288882733 ≤ 288948269)
    (by decide : 288948269 ≤ 289013805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 288882733 289013805).card = 468 := join_1_0

end S137C12
end Sude.GeneratedTwinScan
