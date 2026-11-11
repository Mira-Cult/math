import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20573)) 423231533 423264301 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 423231533 423264301).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20573 423231533 423264301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20574)) 423264301 423297069 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 423264301 423297069).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20574 423264301 423297069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20574)) 423297069 423329837 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 423297069 423329837).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20574 423297069 423329837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20575)) 423329837 423362605 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 423329837 423362605).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20575 423329837 423362605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 423231533 423297069).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 423231533 ≤ 423264301)
    (by decide : 423264301 ≤ 423297069) block0 block1

theorem join_0_1 : (twinPrimeSegment 423297069 423362605).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 423297069 ≤ 423329837)
    (by decide : 423329837 ≤ 423362605) block2 block3

theorem join_1_0 : (twinPrimeSegment 423231533 423362605).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 423231533 ≤ 423297069)
    (by decide : 423297069 ≤ 423362605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 423231533 423362605).card = 473 := join_1_0

end S201C13
end Sude.GeneratedTwinScan
