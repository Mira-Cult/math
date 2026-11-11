import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12579)) 158203949 158236717 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 158203949 158236717).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12579 158203949 158236717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12580)) 158236717 158269485 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 158236717 158269485).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12580 158236717 158269485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12581)) 158269485 158302253 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 158269485 158302253).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12581 158269485 158302253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12583)) 158302253 158335021 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 158302253 158335021).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12583 158302253 158335021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 158203949 158269485).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 158203949 ≤ 158236717)
    (by decide : 158236717 ≤ 158269485) block0 block1

theorem join_0_1 : (twinPrimeSegment 158269485 158335021).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 158269485 ≤ 158302253)
    (by decide : 158302253 ≤ 158335021) block2 block3

theorem join_1_0 : (twinPrimeSegment 158203949 158335021).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 158203949 ≤ 158269485)
    (by decide : 158269485 ≤ 158335021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 158203949 158335021).card = 478 := join_1_0

end S075C07
end Sude.GeneratedTwinScan
