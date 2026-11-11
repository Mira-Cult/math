import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12857)) 165281837 165314605 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 165281837 165314605).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12857 165281837 165314605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12858)) 165314605 165347373 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 165314605 165347373).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12858 165314605 165347373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12860)) 165347373 165380141 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 165347373 165380141).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12860 165347373 165380141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12861)) 165380141 165412909 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 165380141 165412909).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12861 165380141 165412909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 165281837 165347373).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 165281837 ≤ 165314605)
    (by decide : 165314605 ≤ 165347373) block0 block1

theorem join_0_1 : (twinPrimeSegment 165347373 165412909).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 165347373 ≤ 165380141)
    (by decide : 165380141 ≤ 165412909) block2 block3

theorem join_1_0 : (twinPrimeSegment 165281837 165412909).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 165281837 ≤ 165347373)
    (by decide : 165347373 ≤ 165412909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 165281837 165412909).card = 464 := join_1_0

end S078C13
end Sude.GeneratedTwinScan
