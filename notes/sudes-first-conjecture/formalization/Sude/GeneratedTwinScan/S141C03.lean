import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17208)) 296091693 296124461 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 296091693 296124461).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17208 296091693 296124461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17209)) 296124461 296157229 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 296124461 296157229).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17209 296124461 296157229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17210)) 296157229 296189997 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 296157229 296189997).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17210 296157229 296189997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17211)) 296189997 296222765 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 296189997 296222765).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17211 296189997 296222765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 296091693 296157229).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 296091693 ≤ 296124461)
    (by decide : 296124461 ≤ 296157229) block0 block1

theorem join_0_1 : (twinPrimeSegment 296157229 296222765).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 296157229 ≤ 296189997)
    (by decide : 296189997 ≤ 296222765) block2 block3

theorem join_1_0 : (twinPrimeSegment 296091693 296222765).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 296091693 ≤ 296157229)
    (by decide : 296157229 ≤ 296222765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 296091693 296222765).card = 452 := join_1_0

end S141C03
end Sude.GeneratedTwinScan
