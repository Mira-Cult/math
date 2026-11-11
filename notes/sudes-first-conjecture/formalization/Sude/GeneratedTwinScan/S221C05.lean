import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21544)) 464125997 464158765 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 464125997 464158765).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21544 464125997 464158765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21545)) 464158765 464191533 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 464158765 464191533).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21545 464158765 464191533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21545)) 464191533 464224301 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 464191533 464224301).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21545 464191533 464224301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21546)) 464224301 464257069 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 464224301 464257069).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21546 464224301 464257069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 464125997 464191533).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 464125997 ≤ 464158765)
    (by decide : 464158765 ≤ 464191533) block0 block1

theorem join_0_1 : (twinPrimeSegment 464191533 464257069).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 464191533 ≤ 464224301)
    (by decide : 464224301 ≤ 464257069) block2 block3

theorem join_1_0 : (twinPrimeSegment 464125997 464257069).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 464125997 ≤ 464191533)
    (by decide : 464191533 ≤ 464257069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 464125997 464257069).card = 441 := join_1_0

end S221C05
end Sude.GeneratedTwinScan
