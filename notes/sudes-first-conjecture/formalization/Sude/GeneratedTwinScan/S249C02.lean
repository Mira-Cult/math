import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22857)) 522453037 522485805 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 522453037 522485805).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22857 522453037 522485805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22858)) 522485805 522518573 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 522485805 522518573).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22858 522485805 522518573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22859)) 522518573 522551341 = 87 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 522518573 522551341).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22859 522518573 522551341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22860)) 522551341 522584109 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 522551341 522584109).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22860 522551341 522584109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 522453037 522518573).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 522453037 ≤ 522485805)
    (by decide : 522485805 ≤ 522518573) block0 block1

theorem join_0_1 : (twinPrimeSegment 522518573 522584109).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 522518573 ≤ 522551341)
    (by decide : 522551341 ≤ 522584109) block2 block3

theorem join_1_0 : (twinPrimeSegment 522453037 522584109).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 522453037 ≤ 522518573)
    (by decide : 522518573 ≤ 522584109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 522453037 522584109).card = 417 := join_1_0

end S249C02
end Sude.GeneratedTwinScan
