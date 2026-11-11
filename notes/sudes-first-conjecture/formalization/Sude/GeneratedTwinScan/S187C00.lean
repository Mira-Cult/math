import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19804)) 392167469 392200237 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 392167469 392200237).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19804 392167469 392200237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19804)) 392200237 392233005 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 392200237 392233005).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19804 392200237 392233005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19805)) 392233005 392265773 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 392233005 392265773).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19805 392233005 392265773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19806)) 392265773 392298541 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 392265773 392298541).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19806 392265773 392298541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 392167469 392233005).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 392167469 ≤ 392200237)
    (by decide : 392200237 ≤ 392233005) block0 block1

theorem join_0_1 : (twinPrimeSegment 392233005 392298541).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 392233005 ≤ 392265773)
    (by decide : 392265773 ≤ 392298541) block2 block3

theorem join_1_0 : (twinPrimeSegment 392167469 392298541).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 392167469 ≤ 392233005)
    (by decide : 392233005 ≤ 392298541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 392167469 392298541).card = 425 := join_1_0

end S187C00
end Sude.GeneratedTwinScan
