import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13605)) 185073709 185106477 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 185073709 185106477).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13605 185073709 185106477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13606)) 185106477 185139245 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 185106477 185139245).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13606 185106477 185139245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13607)) 185139245 185172013 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 185139245 185172013).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13607 185139245 185172013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13608)) 185172013 185204781 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 185172013 185204781).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13608 185172013 185204781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 185073709 185139245).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 185073709 ≤ 185106477)
    (by decide : 185106477 ≤ 185139245) block0 block1

theorem join_0_1 : (twinPrimeSegment 185139245 185204781).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 185139245 ≤ 185172013)
    (by decide : 185172013 ≤ 185204781) block2 block3

theorem join_1_0 : (twinPrimeSegment 185073709 185204781).card = 523 := by
  simpa using combineTwinPrimeSegments (by decide : 185073709 ≤ 185139245)
    (by decide : 185139245 ≤ 185204781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 185073709 185204781).card = 523 := join_1_0

end S088C04
end Sude.GeneratedTwinScan
