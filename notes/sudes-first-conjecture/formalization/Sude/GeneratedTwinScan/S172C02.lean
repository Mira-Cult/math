import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19000)) 360972333 361005101 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 360972333 361005101).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19000 360972333 361005101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19000)) 361005101 361037869 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 361005101 361037869).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19000 361005101 361037869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19001)) 361037869 361070637 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 361037869 361070637).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19001 361037869 361070637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19002)) 361070637 361103405 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 361070637 361103405).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19002 361070637 361103405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 360972333 361037869).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 360972333 ≤ 361005101)
    (by decide : 361005101 ≤ 361037869) block0 block1

theorem join_0_1 : (twinPrimeSegment 361037869 361103405).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 361037869 ≤ 361070637)
    (by decide : 361070637 ≤ 361103405) block2 block3

theorem join_1_0 : (twinPrimeSegment 360972333 361103405).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 360972333 ≤ 361037869)
    (by decide : 361037869 ≤ 361103405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 360972333 361103405).card = 442 := join_1_0

end S172C02
end Sude.GeneratedTwinScan
