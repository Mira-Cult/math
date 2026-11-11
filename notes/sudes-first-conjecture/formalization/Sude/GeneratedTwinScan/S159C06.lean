import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18282)) 334233645 334266413 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 334233645 334266413).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18282 334233645 334266413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18283)) 334266413 334299181 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 334266413 334299181).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18283 334266413 334299181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18284)) 334299181 334331949 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 334299181 334331949).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18284 334299181 334331949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18285)) 334331949 334364717 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 334331949 334364717).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18285 334331949 334364717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 334233645 334299181).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 334233645 ≤ 334266413)
    (by decide : 334266413 ≤ 334299181) block0 block1

theorem join_0_1 : (twinPrimeSegment 334299181 334364717).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 334299181 ≤ 334331949)
    (by decide : 334331949 ≤ 334364717) block2 block3

theorem join_1_0 : (twinPrimeSegment 334233645 334364717).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 334233645 ≤ 334299181)
    (by decide : 334299181 ≤ 334364717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 334233645 334364717).card = 454 := join_1_0

end S159C06
end Sude.GeneratedTwinScan
