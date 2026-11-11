import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20109)) 404357165 404389933 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 404357165 404389933).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20109 404357165 404389933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20110)) 404389933 404422701 = 83 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 404389933 404422701).card = 83 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20110 404389933 404422701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20111)) 404422701 404455469 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 404422701 404455469).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20111 404422701 404455469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20111)) 404455469 404488237 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 404455469 404488237).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20111 404455469 404488237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 404357165 404422701).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 404357165 ≤ 404389933)
    (by decide : 404389933 ≤ 404422701) block0 block1

theorem join_0_1 : (twinPrimeSegment 404422701 404488237).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 404422701 ≤ 404455469)
    (by decide : 404455469 ≤ 404488237) block2 block3

theorem join_1_0 : (twinPrimeSegment 404357165 404488237).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 404357165 ≤ 404422701)
    (by decide : 404422701 ≤ 404488237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 404357165 404488237).card = 437 := join_1_0

end S192C13
end Sude.GeneratedTwinScan
