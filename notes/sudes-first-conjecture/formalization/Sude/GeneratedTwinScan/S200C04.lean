import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20493)) 419954733 419987501 = 89 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 419954733 419987501).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20493 419954733 419987501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20494)) 419987501 420020269 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 419987501 420020269).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20494 419987501 420020269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20495)) 420020269 420053037 = 89 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 420020269 420053037).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20495 420020269 420053037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20495)) 420053037 420085805 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 420053037 420085805).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20495 420053037 420085805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 419954733 420020269).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 419954733 ≤ 419987501)
    (by decide : 419987501 ≤ 420020269) block0 block1

theorem join_0_1 : (twinPrimeSegment 420020269 420085805).card = 187 := by
  simpa using combineTwinPrimeSegments (by decide : 420020269 ≤ 420053037)
    (by decide : 420053037 ≤ 420085805) block2 block3

theorem join_1_0 : (twinPrimeSegment 419954733 420085805).card = 396 := by
  simpa using combineTwinPrimeSegments (by decide : 419954733 ≤ 420020269)
    (by decide : 420020269 ≤ 420085805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 419954733 420085805).card = 396 := join_1_0

end S200C04
end Sude.GeneratedTwinScan
