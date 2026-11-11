import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19581)) 383385645 383418413 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 383385645 383418413).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19581 383385645 383418413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19581)) 383418413 383451181 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 383418413 383451181).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19581 383418413 383451181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19582)) 383451181 383483949 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 383451181 383483949).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19582 383451181 383483949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19583)) 383483949 383516717 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 383483949 383516717).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19583 383483949 383516717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 383385645 383451181).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 383385645 ≤ 383418413)
    (by decide : 383418413 ≤ 383451181) block0 block1

theorem join_0_1 : (twinPrimeSegment 383451181 383516717).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 383451181 ≤ 383483949)
    (by decide : 383483949 ≤ 383516717) block2 block3

theorem join_1_0 : (twinPrimeSegment 383385645 383516717).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 383385645 ≤ 383451181)
    (by decide : 383451181 ≤ 383516717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 383385645 383516717).card = 477 := join_1_0

end S182C13
end Sude.GeneratedTwinScan
