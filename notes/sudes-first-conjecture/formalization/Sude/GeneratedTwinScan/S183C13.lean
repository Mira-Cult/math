import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19634)) 385482797 385515565 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 385482797 385515565).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19634 385482797 385515565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19635)) 385515565 385548333 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 385515565 385548333).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19635 385515565 385548333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19636)) 385548333 385581101 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 385548333 385581101).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19636 385548333 385581101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19637)) 385581101 385613869 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 385581101 385613869).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19637 385581101 385613869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 385482797 385548333).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 385482797 ≤ 385515565)
    (by decide : 385515565 ≤ 385548333) block0 block1

theorem join_0_1 : (twinPrimeSegment 385548333 385613869).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 385548333 ≤ 385581101)
    (by decide : 385581101 ≤ 385613869) block2 block3

theorem join_1_0 : (twinPrimeSegment 385482797 385613869).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 385482797 ≤ 385548333)
    (by decide : 385548333 ≤ 385613869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 385482797 385613869).card = 432 := join_1_0

end S183C13
end Sude.GeneratedTwinScan
