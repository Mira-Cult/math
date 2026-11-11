import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22601)) 510787629 510820397 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 510787629 510820397).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22601 510787629 510820397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22602)) 510820397 510853165 = 85 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 510820397 510853165).card = 85 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22602 510820397 510853165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22602)) 510853165 510885933 = 86 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 510853165 510885933).card = 86 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22602 510853165 510885933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22603)) 510885933 510918701 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 510885933 510918701).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22603 510885933 510918701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 510787629 510853165).card = 177 := by
  simpa using combineTwinPrimeSegments (by decide : 510787629 ≤ 510820397)
    (by decide : 510820397 ≤ 510853165) block0 block1

theorem join_0_1 : (twinPrimeSegment 510853165 510918701).card = 191 := by
  simpa using combineTwinPrimeSegments (by decide : 510853165 ≤ 510885933)
    (by decide : 510885933 ≤ 510918701) block2 block3

theorem join_1_0 : (twinPrimeSegment 510787629 510918701).card = 368 := by
  simpa using combineTwinPrimeSegments (by decide : 510787629 ≤ 510853165)
    (by decide : 510853165 ≤ 510918701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 510787629 510918701).card = 368 := join_1_0

end S243C09
end Sude.GeneratedTwinScan
