import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22327)) 498466861 498499629 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 498466861 498499629).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22327 498466861 498499629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22327)) 498499629 498532397 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 498499629 498532397).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22327 498499629 498532397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22328)) 498532397 498565165 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 498532397 498565165).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22328 498532397 498565165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22329)) 498565165 498597933 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 498565165 498597933).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22329 498565165 498597933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 498466861 498532397).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 498466861 ≤ 498499629)
    (by decide : 498499629 ≤ 498532397) block0 block1

theorem join_0_1 : (twinPrimeSegment 498532397 498597933).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 498532397 ≤ 498565165)
    (by decide : 498565165 ≤ 498597933) block2 block3

theorem join_1_0 : (twinPrimeSegment 498466861 498597933).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 498466861 ≤ 498532397)
    (by decide : 498532397 ≤ 498597933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 498466861 498597933).card = 414 := join_1_0

end S237C11
end Sude.GeneratedTwinScan
