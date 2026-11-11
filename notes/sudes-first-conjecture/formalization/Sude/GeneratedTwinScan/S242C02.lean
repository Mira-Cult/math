import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22534)) 507772973 507805741 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 507772973 507805741).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22534 507772973 507805741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22535)) 507805741 507838509 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 507805741 507838509).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22535 507805741 507838509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22535)) 507838509 507871277 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 507838509 507871277).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22535 507838509 507871277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22536)) 507871277 507904045 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 507871277 507904045).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22536 507871277 507904045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 507772973 507838509).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 507772973 ≤ 507805741)
    (by decide : 507805741 ≤ 507838509) block0 block1

theorem join_0_1 : (twinPrimeSegment 507838509 507904045).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 507838509 ≤ 507871277)
    (by decide : 507871277 ≤ 507904045) block2 block3

theorem join_1_0 : (twinPrimeSegment 507772973 507904045).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 507772973 ≤ 507838509)
    (by decide : 507838509 ≤ 507904045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 507772973 507904045).card = 433 := join_1_0

end S242C02
end Sude.GeneratedTwinScan
