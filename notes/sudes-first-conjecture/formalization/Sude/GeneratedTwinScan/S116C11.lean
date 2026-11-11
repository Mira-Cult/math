import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15644)) 244711469 244744237 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 244711469 244744237).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15644 244711469 244744237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15645)) 244744237 244777005 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 244744237 244777005).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15645 244744237 244777005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15646)) 244777005 244809773 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 244777005 244809773).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15646 244777005 244809773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15647)) 244809773 244842541 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 244809773 244842541).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15647 244809773 244842541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 244711469 244777005).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 244711469 ≤ 244744237)
    (by decide : 244744237 ≤ 244777005) block0 block1

theorem join_0_1 : (twinPrimeSegment 244777005 244842541).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 244777005 ≤ 244809773)
    (by decide : 244809773 ≤ 244842541) block2 block3

theorem join_1_0 : (twinPrimeSegment 244711469 244842541).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 244711469 ≤ 244777005)
    (by decide : 244777005 ≤ 244842541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 244711469 244842541).card = 480 := join_1_0

end S116C11
end Sude.GeneratedTwinScan
