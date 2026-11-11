import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18167)) 330039341 330072109 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 330039341 330072109).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18167 330039341 330072109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18168)) 330072109 330104877 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 330072109 330104877).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18168 330072109 330104877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18169)) 330104877 330137645 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 330104877 330137645).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18169 330104877 330137645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18170)) 330137645 330170413 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 330137645 330170413).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18170 330137645 330170413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 330039341 330104877).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 330039341 ≤ 330072109)
    (by decide : 330072109 ≤ 330104877) block0 block1

theorem join_0_1 : (twinPrimeSegment 330104877 330170413).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 330104877 ≤ 330137645)
    (by decide : 330137645 ≤ 330170413) block2 block3

theorem join_1_0 : (twinPrimeSegment 330039341 330170413).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 330039341 ≤ 330104877)
    (by decide : 330104877 ≤ 330170413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 330039341 330170413).card = 441 := join_1_0

end S157C06
end Sude.GeneratedTwinScan
