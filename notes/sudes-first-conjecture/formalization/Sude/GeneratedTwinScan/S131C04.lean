import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16591)) 275251245 275284013 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 275251245 275284013).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16591 275251245 275284013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16592)) 275284013 275316781 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 275284013 275316781).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16592 275284013 275316781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16593)) 275316781 275349549 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 275316781 275349549).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16593 275316781 275349549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16594)) 275349549 275382317 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 275349549 275382317).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16594 275349549 275382317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 275251245 275316781).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 275251245 ≤ 275284013)
    (by decide : 275284013 ≤ 275316781) block0 block1

theorem join_0_1 : (twinPrimeSegment 275316781 275382317).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 275316781 ≤ 275349549)
    (by decide : 275349549 ≤ 275382317) block2 block3

theorem join_1_0 : (twinPrimeSegment 275251245 275382317).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 275251245 ≤ 275316781)
    (by decide : 275316781 ≤ 275382317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 275251245 275382317).card = 451 := join_1_0

end S131C04
end Sude.GeneratedTwinScan
