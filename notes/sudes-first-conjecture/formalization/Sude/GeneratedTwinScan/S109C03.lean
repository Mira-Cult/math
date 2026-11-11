import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15133)) 228982829 229015597 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 228982829 229015597).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15133 228982829 229015597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15134)) 229015597 229048365 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 229015597 229048365).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15134 229015597 229048365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15135)) 229048365 229081133 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 229048365 229081133).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15135 229048365 229081133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15136)) 229081133 229113901 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 229081133 229113901).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15136 229081133 229113901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 228982829 229048365).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 228982829 ≤ 229015597)
    (by decide : 229015597 ≤ 229048365) block0 block1

theorem join_0_1 : (twinPrimeSegment 229048365 229113901).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 229048365 ≤ 229081133)
    (by decide : 229081133 ≤ 229113901) block2 block3

theorem join_1_0 : (twinPrimeSegment 228982829 229113901).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 228982829 ≤ 229048365)
    (by decide : 229048365 ≤ 229113901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 228982829 229113901).card = 456 := join_1_0

end S109C03
end Sude.GeneratedTwinScan
