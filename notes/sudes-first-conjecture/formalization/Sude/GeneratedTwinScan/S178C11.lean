import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19358)) 374734893 374767661 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 374734893 374767661).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19358 374734893 374767661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19359)) 374767661 374800429 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 374767661 374800429).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19359 374767661 374800429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19360)) 374800429 374833197 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 374800429 374833197).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19360 374800429 374833197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19361)) 374833197 374865965 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 374833197 374865965).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19361 374833197 374865965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 374734893 374800429).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 374734893 ≤ 374767661)
    (by decide : 374767661 ≤ 374800429) block0 block1

theorem join_0_1 : (twinPrimeSegment 374800429 374865965).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 374800429 ≤ 374833197)
    (by decide : 374833197 ≤ 374865965) block2 block3

theorem join_1_0 : (twinPrimeSegment 374734893 374865965).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 374734893 ≤ 374800429)
    (by decide : 374800429 ≤ 374865965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 374734893 374865965).card = 449 := join_1_0

end S178C11
end Sude.GeneratedTwinScan
