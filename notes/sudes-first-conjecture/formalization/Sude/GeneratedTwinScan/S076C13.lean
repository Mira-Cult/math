import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12693)) 161087533 161120301 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 161087533 161120301).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12693 161087533 161120301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12694)) 161120301 161153069 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 161120301 161153069).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12694 161120301 161153069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12695)) 161153069 161185837 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 161153069 161185837).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12695 161153069 161185837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12697)) 161185837 161218605 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 161185837 161218605).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12697 161185837 161218605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 161087533 161153069).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 161087533 ≤ 161120301)
    (by decide : 161120301 ≤ 161153069) block0 block1

theorem join_0_1 : (twinPrimeSegment 161153069 161218605).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 161153069 ≤ 161185837)
    (by decide : 161185837 ≤ 161218605) block2 block3

theorem join_1_0 : (twinPrimeSegment 161087533 161218605).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 161087533 ≤ 161153069)
    (by decide : 161153069 ≤ 161218605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 161087533 161218605).card = 452 := join_1_0

end S076C13
end Sude.GeneratedTwinScan
