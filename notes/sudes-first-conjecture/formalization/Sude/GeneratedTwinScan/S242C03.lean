import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22537)) 507904045 507936813 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 507904045 507936813).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22537 507904045 507936813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22538)) 507936813 507969581 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 507936813 507969581).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22538 507936813 507969581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22538)) 507969581 508002349 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 507969581 508002349).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22538 507969581 508002349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22539)) 508002349 508035117 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 508002349 508035117).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22539 508002349 508035117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 507904045 507969581).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 507904045 ≤ 507936813)
    (by decide : 507936813 ≤ 507969581) block0 block1

theorem join_0_1 : (twinPrimeSegment 507969581 508035117).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 507969581 ≤ 508002349)
    (by decide : 508002349 ≤ 508035117) block2 block3

theorem join_1_0 : (twinPrimeSegment 507904045 508035117).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 507904045 ≤ 507969581)
    (by decide : 507969581 ≤ 508035117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 507904045 508035117).card = 439 := join_1_0

end S242C03
end Sude.GeneratedTwinScan
