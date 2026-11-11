import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21048)) 443023405 443056173 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 443023405 443056173).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21048 443023405 443056173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21049)) 443056173 443088941 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 443056173 443088941).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21049 443056173 443088941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21050)) 443088941 443121709 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 443088941 443121709).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21050 443088941 443121709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21051)) 443121709 443154477 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 443121709 443154477).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21051 443121709 443154477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 443023405 443088941).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 443023405 ≤ 443056173)
    (by decide : 443056173 ≤ 443088941) block0 block1

theorem join_0_1 : (twinPrimeSegment 443088941 443154477).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 443088941 ≤ 443121709)
    (by decide : 443121709 ≤ 443154477) block2 block3

theorem join_1_0 : (twinPrimeSegment 443023405 443154477).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 443023405 ≤ 443088941)
    (by decide : 443088941 ≤ 443154477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 443023405 443154477).card = 444 := join_1_0

end S211C04
end Sude.GeneratedTwinScan
