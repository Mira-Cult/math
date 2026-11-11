import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15055)) 226623533 226656301 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 226623533 226656301).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15055 226623533 226656301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15056)) 226656301 226689069 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 226656301 226689069).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15056 226656301 226689069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15057)) 226689069 226721837 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 226689069 226721837).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15057 226689069 226721837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15058)) 226721837 226754605 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 226721837 226754605).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15058 226721837 226754605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 226623533 226689069).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 226623533 ≤ 226656301)
    (by decide : 226656301 ≤ 226689069) block0 block1

theorem join_0_1 : (twinPrimeSegment 226689069 226754605).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 226689069 ≤ 226721837)
    (by decide : 226721837 ≤ 226754605) block2 block3

theorem join_1_0 : (twinPrimeSegment 226623533 226754605).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 226623533 ≤ 226689069)
    (by decide : 226689069 ≤ 226754605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 226623533 226754605).card = 468 := join_1_0

end S108C01
end Sude.GeneratedTwinScan
