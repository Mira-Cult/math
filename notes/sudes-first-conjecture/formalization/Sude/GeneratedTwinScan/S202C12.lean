import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20621)) 425197613 425230381 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 425197613 425230381).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20621 425197613 425230381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20621)) 425230381 425263149 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 425230381 425263149).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20621 425230381 425263149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20622)) 425263149 425295917 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 425263149 425295917).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20622 425263149 425295917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20623)) 425295917 425328685 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 425295917 425328685).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20623 425295917 425328685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 425197613 425263149).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 425197613 ≤ 425230381)
    (by decide : 425230381 ≤ 425263149) block0 block1

theorem join_0_1 : (twinPrimeSegment 425263149 425328685).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 425263149 ≤ 425295917)
    (by decide : 425295917 ≤ 425328685) block2 block3

theorem join_1_0 : (twinPrimeSegment 425197613 425328685).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 425197613 ≤ 425263149)
    (by decide : 425263149 ≤ 425328685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 425197613 425328685).card = 440 := join_1_0

end S202C12
end Sude.GeneratedTwinScan
