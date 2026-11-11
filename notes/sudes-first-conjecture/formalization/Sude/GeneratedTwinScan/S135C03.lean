import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16838)) 283508781 283541549 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 283508781 283541549).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16838 283508781 283541549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16839)) 283541549 283574317 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 283541549 283574317).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16839 283541549 283574317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16840)) 283574317 283607085 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 283574317 283607085).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16840 283574317 283607085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16841)) 283607085 283639853 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 283607085 283639853).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16841 283607085 283639853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 283508781 283574317).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 283508781 ≤ 283541549)
    (by decide : 283541549 ≤ 283574317) block0 block1

theorem join_0_1 : (twinPrimeSegment 283574317 283639853).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 283574317 ≤ 283607085)
    (by decide : 283607085 ≤ 283639853) block2 block3

theorem join_1_0 : (twinPrimeSegment 283508781 283639853).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 283508781 ≤ 283574317)
    (by decide : 283574317 ≤ 283639853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 283508781 283639853).card = 478 := join_1_0

end S135C03
end Sude.GeneratedTwinScan
