import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18479)) 341442605 341475373 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 341442605 341475373).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18479 341442605 341475373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18479)) 341475373 341508141 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 341475373 341508141).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18479 341475373 341508141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18480)) 341508141 341540909 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 341508141 341540909).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18480 341508141 341540909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18481)) 341540909 341573677 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 341540909 341573677).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18481 341540909 341573677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 341442605 341508141).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 341442605 ≤ 341475373)
    (by decide : 341475373 ≤ 341508141) block0 block1

theorem join_0_1 : (twinPrimeSegment 341508141 341573677).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 341508141 ≤ 341540909)
    (by decide : 341540909 ≤ 341573677) block2 block3

theorem join_1_0 : (twinPrimeSegment 341442605 341573677).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 341442605 ≤ 341508141)
    (by decide : 341508141 ≤ 341573677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 341442605 341573677).card = 465 := join_1_0

end S162C13
end Sude.GeneratedTwinScan
