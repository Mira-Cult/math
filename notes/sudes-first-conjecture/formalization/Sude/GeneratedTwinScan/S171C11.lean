import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18975)) 360054829 360087597 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 360054829 360087597).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18975 360054829 360087597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18976)) 360087597 360120365 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 360087597 360120365).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18976 360087597 360120365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18977)) 360120365 360153133 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 360120365 360153133).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18977 360120365 360153133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18978)) 360153133 360185901 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 360153133 360185901).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18978 360153133 360185901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 360054829 360120365).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 360054829 ≤ 360087597)
    (by decide : 360087597 ≤ 360120365) block0 block1

theorem join_0_1 : (twinPrimeSegment 360120365 360185901).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 360120365 ≤ 360153133)
    (by decide : 360153133 ≤ 360185901) block2 block3

theorem join_1_0 : (twinPrimeSegment 360054829 360185901).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 360054829 ≤ 360120365)
    (by decide : 360120365 ≤ 360185901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 360054829 360185901).card = 437 := join_1_0

end S171C11
end Sude.GeneratedTwinScan
