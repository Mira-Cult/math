import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20027)) 401080365 401113133 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 401080365 401113133).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20027 401080365 401113133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20028)) 401113133 401145901 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 401113133 401145901).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20028 401113133 401145901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20029)) 401145901 401178669 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 401145901 401178669).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20029 401145901 401178669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20030)) 401178669 401211437 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 401178669 401211437).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20030 401178669 401211437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 401080365 401145901).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 401080365 ≤ 401113133)
    (by decide : 401113133 ≤ 401145901) block0 block1

theorem join_0_1 : (twinPrimeSegment 401145901 401211437).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 401145901 ≤ 401178669)
    (by decide : 401178669 ≤ 401211437) block2 block3

theorem join_1_0 : (twinPrimeSegment 401080365 401211437).card = 402 := by
  simpa using combineTwinPrimeSegments (by decide : 401080365 ≤ 401145901)
    (by decide : 401145901 ≤ 401211437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 401080365 401211437).card = 402 := join_1_0

end S191C04
end Sude.GeneratedTwinScan
