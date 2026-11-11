import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21163)) 447873069 447905837 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 447873069 447905837).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21163 447873069 447905837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21164)) 447905837 447938605 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 447905837 447938605).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21164 447905837 447938605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21165)) 447938605 447971373 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 447938605 447971373).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21165 447938605 447971373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21166)) 447971373 448004141 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 447971373 448004141).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21166 447971373 448004141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 447873069 447938605).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 447873069 ≤ 447905837)
    (by decide : 447905837 ≤ 447938605) block0 block1

theorem join_0_1 : (twinPrimeSegment 447938605 448004141).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 447938605 ≤ 447971373)
    (by decide : 447971373 ≤ 448004141) block2 block3

theorem join_1_0 : (twinPrimeSegment 447873069 448004141).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 447873069 ≤ 447938605)
    (by decide : 447938605 ≤ 448004141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 447873069 448004141).card = 433 := join_1_0

end S213C09
end Sude.GeneratedTwinScan
