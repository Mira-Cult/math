import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16912)) 285999149 286031917 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 285999149 286031917).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16912 285999149 286031917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16913)) 286031917 286064685 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 286031917 286064685).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16913 286031917 286064685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16914)) 286064685 286097453 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 286064685 286097453).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16914 286064685 286097453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16915)) 286097453 286130221 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 286097453 286130221).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16915 286097453 286130221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 285999149 286064685).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 285999149 ≤ 286031917)
    (by decide : 286031917 ≤ 286064685) block0 block1

theorem join_0_1 : (twinPrimeSegment 286064685 286130221).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 286064685 ≤ 286097453)
    (by decide : 286097453 ≤ 286130221) block2 block3

theorem join_1_0 : (twinPrimeSegment 285999149 286130221).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 285999149 ≤ 286064685)
    (by decide : 286064685 ≤ 286130221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 285999149 286130221).card = 467 := join_1_0

end S136C06
end Sude.GeneratedTwinScan
