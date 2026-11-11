import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13342)) 177995821 178028589 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 177995821 178028589).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13342 177995821 178028589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13343)) 178028589 178061357 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 178028589 178061357).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13343 178028589 178061357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13345)) 178061357 178094125 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 178061357 178094125).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13345 178061357 178094125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13346)) 178094125 178126893 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 178094125 178126893).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13346 178094125 178126893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 177995821 178061357).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 177995821 ≤ 178028589)
    (by decide : 178028589 ≤ 178061357) block0 block1

theorem join_0_1 : (twinPrimeSegment 178061357 178126893).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 178061357 ≤ 178094125)
    (by decide : 178094125 ≤ 178126893) block2 block3

theorem join_1_0 : (twinPrimeSegment 177995821 178126893).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 177995821 ≤ 178061357)
    (by decide : 178061357 ≤ 178126893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 177995821 178126893).card = 468 := join_1_0

end S084C14
end Sude.GeneratedTwinScan
