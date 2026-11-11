import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19614)) 384696365 384729133 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 384696365 384729133).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19614 384696365 384729133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19615)) 384729133 384761901 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 384729133 384761901).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19615 384729133 384761901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19616)) 384761901 384794669 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 384761901 384794669).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19616 384761901 384794669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19617)) 384794669 384827437 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 384794669 384827437).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19617 384794669 384827437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 384696365 384761901).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 384696365 ≤ 384729133)
    (by decide : 384729133 ≤ 384761901) block0 block1

theorem join_0_1 : (twinPrimeSegment 384761901 384827437).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 384761901 ≤ 384794669)
    (by decide : 384794669 ≤ 384827437) block2 block3

theorem join_1_0 : (twinPrimeSegment 384696365 384827437).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 384696365 ≤ 384761901)
    (by decide : 384761901 ≤ 384827437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 384696365 384827437).card = 456 := join_1_0

end S183C07
end Sude.GeneratedTwinScan
