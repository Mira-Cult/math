import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15403)) 237240365 237273133 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 237240365 237273133).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15403 237240365 237273133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15404)) 237273133 237305901 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 237273133 237305901).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15404 237273133 237305901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15405)) 237305901 237338669 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 237305901 237338669).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15405 237305901 237338669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15406)) 237338669 237371437 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 237338669 237371437).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15406 237338669 237371437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 237240365 237305901).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 237240365 ≤ 237273133)
    (by decide : 237273133 ≤ 237305901) block0 block1

theorem join_0_1 : (twinPrimeSegment 237305901 237371437).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 237305901 ≤ 237338669)
    (by decide : 237338669 ≤ 237371437) block2 block3

theorem join_1_0 : (twinPrimeSegment 237240365 237371437).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 237240365 ≤ 237305901)
    (by decide : 237305901 ≤ 237371437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 237240365 237371437).card = 443 := join_1_0

end S113C02
end Sude.GeneratedTwinScan
