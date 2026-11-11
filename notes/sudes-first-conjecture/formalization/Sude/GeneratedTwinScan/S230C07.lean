import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21983)) 483262509 483295277 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 483262509 483295277).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21983 483262509 483295277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21984)) 483295277 483328045 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 483295277 483328045).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21984 483295277 483328045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21985)) 483328045 483360813 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 483328045 483360813).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21985 483328045 483360813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21986)) 483360813 483393581 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 483360813 483393581).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21986 483360813 483393581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 483262509 483328045).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 483262509 ≤ 483295277)
    (by decide : 483295277 ≤ 483328045) block0 block1

theorem join_0_1 : (twinPrimeSegment 483328045 483393581).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 483328045 ≤ 483360813)
    (by decide : 483360813 ≤ 483393581) block2 block3

theorem join_1_0 : (twinPrimeSegment 483262509 483393581).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 483262509 ≤ 483328045)
    (by decide : 483328045 ≤ 483393581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 483262509 483393581).card = 429 := join_1_0

end S230C07
end Sude.GeneratedTwinScan
