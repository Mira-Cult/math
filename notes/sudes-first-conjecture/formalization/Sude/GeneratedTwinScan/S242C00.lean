import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22528)) 507510829 507543597 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 507510829 507543597).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22528 507510829 507543597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22529)) 507543597 507576365 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 507543597 507576365).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22529 507543597 507576365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22530)) 507576365 507609133 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 507576365 507609133).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22530 507576365 507609133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22530)) 507609133 507641901 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 507609133 507641901).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22530 507609133 507641901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 507510829 507576365).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 507510829 ≤ 507543597)
    (by decide : 507543597 ≤ 507576365) block0 block1

theorem join_0_1 : (twinPrimeSegment 507576365 507641901).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 507576365 ≤ 507609133)
    (by decide : 507609133 ≤ 507641901) block2 block3

theorem join_1_0 : (twinPrimeSegment 507510829 507641901).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 507510829 ≤ 507576365)
    (by decide : 507576365 ≤ 507641901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 507510829 507641901).card = 447 := join_1_0

end S242C00
end Sude.GeneratedTwinScan
