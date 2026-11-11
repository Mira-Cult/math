import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16468)) 271188013 271220781 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 271188013 271220781).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16468 271188013 271220781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16469)) 271220781 271253549 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 271220781 271253549).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16469 271220781 271253549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16470)) 271253549 271286317 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 271253549 271286317).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16470 271253549 271286317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16471)) 271286317 271319085 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 271286317 271319085).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16471 271286317 271319085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 271188013 271253549).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 271188013 ≤ 271220781)
    (by decide : 271220781 ≤ 271253549) block0 block1

theorem join_0_1 : (twinPrimeSegment 271253549 271319085).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 271253549 ≤ 271286317)
    (by decide : 271286317 ≤ 271319085) block2 block3

theorem join_1_0 : (twinPrimeSegment 271188013 271319085).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 271188013 ≤ 271253549)
    (by decide : 271253549 ≤ 271319085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 271188013 271319085).card = 445 := join_1_0

end S129C05
end Sude.GeneratedTwinScan
