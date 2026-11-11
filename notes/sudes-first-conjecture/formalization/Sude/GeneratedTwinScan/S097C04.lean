import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14282)) 203948077 203980845 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 203948077 203980845).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14282 203948077 203980845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14283)) 203980845 204013613 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 203980845 204013613).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14283 203980845 204013613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14284)) 204013613 204046381 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 204013613 204046381).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14284 204013613 204046381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14285)) 204046381 204079149 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 204046381 204079149).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14285 204046381 204079149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 203948077 204013613).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 203948077 ≤ 203980845)
    (by decide : 203980845 ≤ 204013613) block0 block1

theorem join_0_1 : (twinPrimeSegment 204013613 204079149).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 204013613 ≤ 204046381)
    (by decide : 204046381 ≤ 204079149) block2 block3

theorem join_1_0 : (twinPrimeSegment 203948077 204079149).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 203948077 ≤ 204013613)
    (by decide : 204013613 ≤ 204079149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 203948077 204079149).card = 489 := join_1_0

end S097C04
end Sude.GeneratedTwinScan
