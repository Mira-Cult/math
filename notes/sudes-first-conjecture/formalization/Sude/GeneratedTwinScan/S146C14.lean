import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17551)) 308019245 308052013 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 308019245 308052013).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17551 308019245 308052013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17552)) 308052013 308084781 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 308052013 308084781).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17552 308052013 308084781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17553)) 308084781 308117549 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 308084781 308117549).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17553 308084781 308117549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17554)) 308117549 308150317 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 308117549 308150317).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17554 308117549 308150317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 308019245 308084781).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 308019245 ≤ 308052013)
    (by decide : 308052013 ≤ 308084781) block0 block1

theorem join_0_1 : (twinPrimeSegment 308084781 308150317).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 308084781 ≤ 308117549)
    (by decide : 308117549 ≤ 308150317) block2 block3

theorem join_1_0 : (twinPrimeSegment 308019245 308150317).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 308019245 ≤ 308084781)
    (by decide : 308084781 ≤ 308150317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 308019245 308150317).card = 458 := join_1_0

end S146C14
end Sude.GeneratedTwinScan
