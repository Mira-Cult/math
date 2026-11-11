import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18493)) 341966893 341999661 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 341966893 341999661).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18493 341966893 341999661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18494)) 341999661 342032429 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 341999661 342032429).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18494 341999661 342032429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18495)) 342032429 342065197 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 342032429 342065197).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18495 342032429 342065197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18495)) 342065197 342097965 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 342065197 342097965).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18495 342065197 342097965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 341966893 342032429).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 341966893 ≤ 341999661)
    (by decide : 341999661 ≤ 342032429) block0 block1

theorem join_0_1 : (twinPrimeSegment 342032429 342097965).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 342032429 ≤ 342065197)
    (by decide : 342065197 ≤ 342097965) block2 block3

theorem join_1_0 : (twinPrimeSegment 341966893 342097965).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 341966893 ≤ 342032429)
    (by decide : 342032429 ≤ 342097965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 341966893 342097965).card = 467 := join_1_0

end S163C01
end Sude.GeneratedTwinScan
