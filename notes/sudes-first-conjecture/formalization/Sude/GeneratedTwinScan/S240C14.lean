import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22476)) 505151533 505184301 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 505151533 505184301).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22476 505151533 505184301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22477)) 505184301 505217069 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 505184301 505217069).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22477 505184301 505217069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22477)) 505217069 505249837 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 505217069 505249837).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22477 505217069 505249837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22478)) 505249837 505282605 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 505249837 505282605).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22478 505249837 505282605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 505151533 505217069).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 505151533 ≤ 505184301)
    (by decide : 505184301 ≤ 505217069) block0 block1

theorem join_0_1 : (twinPrimeSegment 505217069 505282605).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 505217069 ≤ 505249837)
    (by decide : 505249837 ≤ 505282605) block2 block3

theorem join_1_0 : (twinPrimeSegment 505151533 505282605).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 505151533 ≤ 505217069)
    (by decide : 505217069 ≤ 505282605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 505151533 505282605).card = 426 := join_1_0

end S240C14
end Sude.GeneratedTwinScan
