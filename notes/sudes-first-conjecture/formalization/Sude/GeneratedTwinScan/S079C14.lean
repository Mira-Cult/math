import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12943)) 167510061 167542829 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 167510061 167542829).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12943 167510061 167542829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12945)) 167542829 167575597 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 167542829 167575597).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12945 167542829 167575597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12946)) 167575597 167608365 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 167575597 167608365).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12946 167575597 167608365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12947)) 167608365 167641133 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 167608365 167641133).card = 142 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12947 167608365 167641133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 167510061 167575597).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 167510061 ≤ 167542829)
    (by decide : 167542829 ≤ 167575597) block0 block1

theorem join_0_1 : (twinPrimeSegment 167575597 167641133).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 167575597 ≤ 167608365)
    (by decide : 167608365 ≤ 167641133) block2 block3

theorem join_1_0 : (twinPrimeSegment 167510061 167641133).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 167510061 ≤ 167575597)
    (by decide : 167575597 ≤ 167641133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 167510061 167641133).card = 510 := join_1_0

end S079C14
end Sude.GeneratedTwinScan
