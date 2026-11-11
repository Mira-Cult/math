import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22170)) 491520045 491552813 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 491520045 491552813).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22170 491520045 491552813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22171)) 491552813 491585581 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 491552813 491585581).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22171 491552813 491585581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22172)) 491585581 491618349 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 491585581 491618349).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22172 491585581 491618349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22173)) 491618349 491651117 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 491618349 491651117).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22173 491618349 491651117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 491520045 491585581).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 491520045 ≤ 491552813)
    (by decide : 491552813 ≤ 491585581) block0 block1

theorem join_0_1 : (twinPrimeSegment 491585581 491651117).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 491585581 ≤ 491618349)
    (by decide : 491618349 ≤ 491651117) block2 block3

theorem join_1_0 : (twinPrimeSegment 491520045 491651117).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 491520045 ≤ 491585581)
    (by decide : 491585581 ≤ 491651117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 491520045 491651117).card = 426 := join_1_0

end S234C06
end Sude.GeneratedTwinScan
