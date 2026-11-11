import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17614)) 310247469 310280237 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 310247469 310280237).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17614 310247469 310280237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17615)) 310280237 310313005 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 310280237 310313005).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17615 310280237 310313005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17616)) 310313005 310345773 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 310313005 310345773).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17616 310313005 310345773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17617)) 310345773 310378541 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 310345773 310378541).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17617 310345773 310378541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 310247469 310313005).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 310247469 ≤ 310280237)
    (by decide : 310280237 ≤ 310313005) block0 block1

theorem join_0_1 : (twinPrimeSegment 310313005 310378541).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 310313005 ≤ 310345773)
    (by decide : 310345773 ≤ 310378541) block2 block3

theorem join_1_0 : (twinPrimeSegment 310247469 310378541).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 310247469 ≤ 310313005)
    (by decide : 310313005 ≤ 310378541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 310247469 310378541).card = 466 := join_1_0

end S147C15
end Sude.GeneratedTwinScan
