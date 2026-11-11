import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13924)) 193855533 193888301 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 193855533 193888301).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13924 193855533 193888301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13925)) 193888301 193921069 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 193888301 193921069).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13925 193888301 193921069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13926)) 193921069 193953837 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 193921069 193953837).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13926 193921069 193953837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13927)) 193953837 193986605 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 193953837 193986605).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13927 193953837 193986605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 193855533 193921069).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 193855533 ≤ 193888301)
    (by decide : 193888301 ≤ 193921069) block0 block1

theorem join_0_1 : (twinPrimeSegment 193921069 193986605).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 193921069 ≤ 193953837)
    (by decide : 193953837 ≤ 193986605) block2 block3

theorem join_1_0 : (twinPrimeSegment 193855533 193986605).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 193855533 ≤ 193921069)
    (by decide : 193921069 ≤ 193986605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 193855533 193986605).card = 484 := join_1_0

end S092C07
end Sude.GeneratedTwinScan
