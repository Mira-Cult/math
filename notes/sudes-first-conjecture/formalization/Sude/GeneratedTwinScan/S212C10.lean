import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21117)) 445906989 445939757 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 445906989 445939757).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21117 445906989 445939757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21118)) 445939757 445972525 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 445939757 445972525).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21118 445939757 445972525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21118)) 445972525 446005293 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 445972525 446005293).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21118 445972525 446005293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21119)) 446005293 446038061 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 446005293 446038061).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21119 446005293 446038061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 445906989 445972525).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 445906989 ≤ 445939757)
    (by decide : 445939757 ≤ 445972525) block0 block1

theorem join_0_1 : (twinPrimeSegment 445972525 446038061).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 445972525 ≤ 446005293)
    (by decide : 446005293 ≤ 446038061) block2 block3

theorem join_1_0 : (twinPrimeSegment 445906989 446038061).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 445906989 ≤ 445972525)
    (by decide : 445972525 ≤ 446038061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 445906989 446038061).card = 446 := join_1_0

end S212C10
end Sude.GeneratedTwinScan
