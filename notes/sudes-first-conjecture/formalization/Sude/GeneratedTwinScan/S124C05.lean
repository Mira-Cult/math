import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16147)) 260702253 260735021 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 260702253 260735021).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16147 260702253 260735021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16148)) 260735021 260767789 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 260735021 260767789).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16148 260735021 260767789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16149)) 260767789 260800557 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 260767789 260800557).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16149 260767789 260800557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16150)) 260800557 260833325 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 260800557 260833325).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16150 260800557 260833325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 260702253 260767789).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 260702253 ≤ 260735021)
    (by decide : 260735021 ≤ 260767789) block0 block1

theorem join_0_1 : (twinPrimeSegment 260767789 260833325).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 260767789 ≤ 260800557)
    (by decide : 260800557 ≤ 260833325) block2 block3

theorem join_1_0 : (twinPrimeSegment 260702253 260833325).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 260702253 ≤ 260767789)
    (by decide : 260767789 ≤ 260833325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 260702253 260833325).card = 476 := join_1_0

end S124C05
end Sude.GeneratedTwinScan
