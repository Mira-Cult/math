import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21498)) 462159917 462192685 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 462159917 462192685).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21498 462159917 462192685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21499)) 462192685 462225453 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 462192685 462225453).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21499 462192685 462225453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21500)) 462225453 462258221 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 462225453 462258221).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21500 462225453 462258221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21500)) 462258221 462290989 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 462258221 462290989).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21500 462258221 462290989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 462159917 462225453).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 462159917 ≤ 462192685)
    (by decide : 462192685 ≤ 462225453) block0 block1

theorem join_0_1 : (twinPrimeSegment 462225453 462290989).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 462225453 ≤ 462258221)
    (by decide : 462258221 ≤ 462290989) block2 block3

theorem join_1_0 : (twinPrimeSegment 462159917 462290989).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 462159917 ≤ 462225453)
    (by decide : 462225453 ≤ 462290989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 462159917 462290989).card = 415 := join_1_0

end S220C06
end Sude.GeneratedTwinScan
