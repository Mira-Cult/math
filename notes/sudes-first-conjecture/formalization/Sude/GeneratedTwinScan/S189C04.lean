import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19922)) 396886061 396918829 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 396886061 396918829).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19922 396886061 396918829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19923)) 396918829 396951597 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 396918829 396951597).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19923 396918829 396951597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19924)) 396951597 396984365 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 396951597 396984365).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19924 396951597 396984365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19925)) 396984365 397017133 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 396984365 397017133).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19925 396984365 397017133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 396886061 396951597).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 396886061 ≤ 396918829)
    (by decide : 396918829 ≤ 396951597) block0 block1

theorem join_0_1 : (twinPrimeSegment 396951597 397017133).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 396951597 ≤ 396984365)
    (by decide : 396984365 ≤ 397017133) block2 block3

theorem join_1_0 : (twinPrimeSegment 396886061 397017133).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 396886061 ≤ 396951597)
    (by decide : 396951597 ≤ 397017133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 396886061 397017133).card = 451 := join_1_0

end S189C04
end Sude.GeneratedTwinScan
