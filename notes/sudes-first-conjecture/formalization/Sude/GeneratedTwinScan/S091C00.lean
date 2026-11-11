import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13815)) 190840877 190873645 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 190840877 190873645).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13815 190840877 190873645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13816)) 190873645 190906413 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 190873645 190906413).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13816 190873645 190906413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13818)) 190906413 190939181 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 190906413 190939181).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13818 190906413 190939181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13819)) 190939181 190971949 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 190939181 190971949).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13819 190939181 190971949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 190840877 190906413).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 190840877 ≤ 190873645)
    (by decide : 190873645 ≤ 190906413) block0 block1

theorem join_0_1 : (twinPrimeSegment 190906413 190971949).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 190906413 ≤ 190939181)
    (by decide : 190939181 ≤ 190971949) block2 block3

theorem join_1_0 : (twinPrimeSegment 190840877 190971949).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 190840877 ≤ 190906413)
    (by decide : 190906413 ≤ 190971949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 190840877 190971949).card = 448 := join_1_0

end S091C00
end Sude.GeneratedTwinScan
