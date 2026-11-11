import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20798)) 432537645 432570413 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 432537645 432570413).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20798 432537645 432570413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20799)) 432570413 432603181 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 432570413 432603181).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20799 432570413 432603181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20799)) 432603181 432635949 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 432603181 432635949).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20799 432603181 432635949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20800)) 432635949 432668717 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 432635949 432668717).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20800 432635949 432668717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 432537645 432603181).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 432537645 ≤ 432570413)
    (by decide : 432570413 ≤ 432603181) block0 block1

theorem join_0_1 : (twinPrimeSegment 432603181 432668717).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 432603181 ≤ 432635949)
    (by decide : 432635949 ≤ 432668717) block2 block3

theorem join_1_0 : (twinPrimeSegment 432537645 432668717).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 432537645 ≤ 432603181)
    (by decide : 432603181 ≤ 432668717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 432537645 432668717).card = 439 := join_1_0

end S206C04
end Sude.GeneratedTwinScan
