import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17865)) 319160365 319193133 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 319160365 319193133).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17865 319160365 319193133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17866)) 319193133 319225901 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 319193133 319225901).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17866 319193133 319225901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17867)) 319225901 319258669 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 319225901 319258669).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17867 319225901 319258669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17868)) 319258669 319291437 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 319258669 319291437).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17868 319258669 319291437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 319160365 319225901).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 319160365 ≤ 319193133)
    (by decide : 319193133 ≤ 319225901) block0 block1

theorem join_0_1 : (twinPrimeSegment 319225901 319291437).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 319225901 ≤ 319258669)
    (by decide : 319258669 ≤ 319291437) block2 block3

theorem join_1_0 : (twinPrimeSegment 319160365 319291437).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 319160365 ≤ 319225901)
    (by decide : 319225901 ≤ 319291437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 319160365 319291437).card = 452 := join_1_0

end S152C03
end Sude.GeneratedTwinScan
