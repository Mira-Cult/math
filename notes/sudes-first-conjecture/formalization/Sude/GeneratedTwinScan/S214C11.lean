import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21219)) 450232365 450265133 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 450232365 450265133).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21219 450232365 450265133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21220)) 450265133 450297901 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 450265133 450297901).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21220 450265133 450297901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21220)) 450297901 450330669 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 450297901 450330669).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21220 450297901 450330669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21221)) 450330669 450363437 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 450330669 450363437).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21221 450330669 450363437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 450232365 450297901).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 450232365 ≤ 450265133)
    (by decide : 450265133 ≤ 450297901) block0 block1

theorem join_0_1 : (twinPrimeSegment 450297901 450363437).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 450297901 ≤ 450330669)
    (by decide : 450330669 ≤ 450363437) block2 block3

theorem join_1_0 : (twinPrimeSegment 450232365 450363437).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 450232365 ≤ 450297901)
    (by decide : 450297901 ≤ 450363437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 450232365 450363437).card = 456 := join_1_0

end S214C11
end Sude.GeneratedTwinScan
