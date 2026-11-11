import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21789)) 474742829 474775597 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 474742829 474775597).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21789 474742829 474775597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21790)) 474775597 474808365 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 474775597 474808365).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21790 474775597 474808365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21790)) 474808365 474841133 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 474808365 474841133).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21790 474808365 474841133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21791)) 474841133 474873901 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 474841133 474873901).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21791 474841133 474873901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 474742829 474808365).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 474742829 ≤ 474775597)
    (by decide : 474775597 ≤ 474808365) block0 block1

theorem join_0_1 : (twinPrimeSegment 474808365 474873901).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 474808365 ≤ 474841133)
    (by decide : 474841133 ≤ 474873901) block2 block3

theorem join_1_0 : (twinPrimeSegment 474742829 474873901).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 474742829 ≤ 474808365)
    (by decide : 474808365 ≤ 474873901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 474742829 474873901).card = 421 := join_1_0

end S226C06
end Sude.GeneratedTwinScan
