import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18475)) 341311533 341344301 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 341311533 341344301).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18475 341311533 341344301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18476)) 341344301 341377069 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 341344301 341377069).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18476 341344301 341377069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18477)) 341377069 341409837 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 341377069 341409837).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18477 341377069 341409837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18478)) 341409837 341442605 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 341409837 341442605).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18478 341409837 341442605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 341311533 341377069).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 341311533 ≤ 341344301)
    (by decide : 341344301 ≤ 341377069) block0 block1

theorem join_0_1 : (twinPrimeSegment 341377069 341442605).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 341377069 ≤ 341409837)
    (by decide : 341409837 ≤ 341442605) block2 block3

theorem join_1_0 : (twinPrimeSegment 341311533 341442605).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 341311533 ≤ 341377069)
    (by decide : 341377069 ≤ 341442605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 341311533 341442605).card = 476 := join_1_0

end S162C12
end Sude.GeneratedTwinScan
