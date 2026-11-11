import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13643)) 186122285 186155053 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 186122285 186155053).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13643 186122285 186155053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13645)) 186155053 186187821 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 186155053 186187821).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13645 186155053 186187821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13646)) 186187821 186220589 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 186187821 186220589).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13646 186187821 186220589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13647)) 186220589 186253357 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 186220589 186253357).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13647 186220589 186253357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 186122285 186187821).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 186122285 ≤ 186155053)
    (by decide : 186155053 ≤ 186187821) block0 block1

theorem join_0_1 : (twinPrimeSegment 186187821 186253357).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 186187821 ≤ 186220589)
    (by decide : 186220589 ≤ 186253357) block2 block3

theorem join_1_0 : (twinPrimeSegment 186122285 186253357).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 186122285 ≤ 186187821)
    (by decide : 186187821 ≤ 186253357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 186122285 186253357).card = 489 := join_1_0

end S088C12
end Sude.GeneratedTwinScan
