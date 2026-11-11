import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13552)) 183631917 183664685 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 183631917 183664685).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13552 183631917 183664685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13553)) 183664685 183697453 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 183664685 183697453).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13553 183664685 183697453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13554)) 183697453 183730221 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 183697453 183730221).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13554 183697453 183730221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13555)) 183730221 183762989 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 183730221 183762989).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13555 183730221 183762989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 183631917 183697453).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 183631917 ≤ 183664685)
    (by decide : 183664685 ≤ 183697453) block0 block1

theorem join_0_1 : (twinPrimeSegment 183697453 183762989).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 183697453 ≤ 183730221)
    (by decide : 183730221 ≤ 183762989) block2 block3

theorem join_1_0 : (twinPrimeSegment 183631917 183762989).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 183631917 ≤ 183697453)
    (by decide : 183697453 ≤ 183762989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 183631917 183762989).card = 487 := join_1_0

end S087C09
end Sude.GeneratedTwinScan
