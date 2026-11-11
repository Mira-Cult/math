import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13914)) 193593389 193626157 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 193593389 193626157).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13914 193593389 193626157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13916)) 193626157 193658925 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 193626157 193658925).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13916 193626157 193658925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13917)) 193658925 193691693 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 193658925 193691693).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13917 193658925 193691693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13918)) 193691693 193724461 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 193691693 193724461).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13918 193691693 193724461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 193593389 193658925).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 193593389 ≤ 193626157)
    (by decide : 193626157 ≤ 193658925) block0 block1

theorem join_0_1 : (twinPrimeSegment 193658925 193724461).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 193658925 ≤ 193691693)
    (by decide : 193691693 ≤ 193724461) block2 block3

theorem join_1_0 : (twinPrimeSegment 193593389 193724461).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 193593389 ≤ 193658925)
    (by decide : 193658925 ≤ 193724461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 193593389 193724461).card = 483 := join_1_0

end S092C05
end Sude.GeneratedTwinScan
