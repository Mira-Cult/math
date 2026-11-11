import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16579)) 274858029 274890797 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 274858029 274890797).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16579 274858029 274890797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16580)) 274890797 274923565 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 274890797 274923565).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16580 274890797 274923565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16581)) 274923565 274956333 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 274923565 274956333).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16581 274923565 274956333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16582)) 274956333 274989101 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 274956333 274989101).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16582 274956333 274989101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 274858029 274923565).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 274858029 ≤ 274890797)
    (by decide : 274890797 ≤ 274923565) block0 block1

theorem join_0_1 : (twinPrimeSegment 274923565 274989101).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 274923565 ≤ 274956333)
    (by decide : 274956333 ≤ 274989101) block2 block3

theorem join_1_0 : (twinPrimeSegment 274858029 274989101).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 274858029 ≤ 274923565)
    (by decide : 274923565 ≤ 274989101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 274858029 274989101).card = 429 := join_1_0

end S131C01
end Sude.GeneratedTwinScan
