import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18865)) 355860525 355893293 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 355860525 355893293).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18865 355860525 355893293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18866)) 355893293 355926061 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 355893293 355926061).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18866 355893293 355926061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18866)) 355926061 355958829 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 355926061 355958829).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18866 355926061 355958829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18867)) 355958829 355991597 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 355958829 355991597).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18867 355958829 355991597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 355860525 355926061).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 355860525 ≤ 355893293)
    (by decide : 355893293 ≤ 355926061) block0 block1

theorem join_0_1 : (twinPrimeSegment 355926061 355991597).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 355926061 ≤ 355958829)
    (by decide : 355958829 ≤ 355991597) block2 block3

theorem join_1_0 : (twinPrimeSegment 355860525 355991597).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 355860525 ≤ 355926061)
    (by decide : 355926061 ≤ 355991597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 355860525 355991597).card = 446 := join_1_0

end S169C11
end Sude.GeneratedTwinScan
