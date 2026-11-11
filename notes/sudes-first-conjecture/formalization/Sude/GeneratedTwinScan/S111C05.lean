import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15279)) 233439277 233472045 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 233439277 233472045).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15279 233439277 233472045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15280)) 233472045 233504813 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 233472045 233504813).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15280 233472045 233504813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15281)) 233504813 233537581 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 233504813 233537581).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15281 233504813 233537581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15283)) 233537581 233570349 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 233537581 233570349).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15283 233537581 233570349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 233439277 233504813).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 233439277 ≤ 233472045)
    (by decide : 233472045 ≤ 233504813) block0 block1

theorem join_0_1 : (twinPrimeSegment 233504813 233570349).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 233504813 ≤ 233537581)
    (by decide : 233537581 ≤ 233570349) block2 block3

theorem join_1_0 : (twinPrimeSegment 233439277 233570349).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 233439277 ≤ 233504813)
    (by decide : 233504813 ≤ 233570349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 233439277 233570349).card = 478 := join_1_0

end S111C05
end Sude.GeneratedTwinScan
