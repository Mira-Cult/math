import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17880)) 319684653 319717421 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 319684653 319717421).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17880 319684653 319717421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17881)) 319717421 319750189 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 319717421 319750189).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17881 319717421 319750189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17882)) 319750189 319782957 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 319750189 319782957).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17882 319750189 319782957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17883)) 319782957 319815725 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 319782957 319815725).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17883 319782957 319815725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 319684653 319750189).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 319684653 ≤ 319717421)
    (by decide : 319717421 ≤ 319750189) block0 block1

theorem join_0_1 : (twinPrimeSegment 319750189 319815725).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 319750189 ≤ 319782957)
    (by decide : 319782957 ≤ 319815725) block2 block3

theorem join_1_0 : (twinPrimeSegment 319684653 319815725).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 319684653 ≤ 319750189)
    (by decide : 319750189 ≤ 319815725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 319684653 319815725).card = 498 := join_1_0

end S152C07
end Sude.GeneratedTwinScan
