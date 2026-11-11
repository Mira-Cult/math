import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19270)) 371327021 371359789 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 371327021 371359789).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19270 371327021 371359789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19271)) 371359789 371392557 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 371359789 371392557).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19271 371359789 371392557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19272)) 371392557 371425325 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 371392557 371425325).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19272 371392557 371425325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19273)) 371425325 371458093 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 371425325 371458093).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19273 371425325 371458093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 371327021 371392557).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 371327021 ≤ 371359789)
    (by decide : 371359789 ≤ 371392557) block0 block1

theorem join_0_1 : (twinPrimeSegment 371392557 371458093).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 371392557 ≤ 371425325)
    (by decide : 371425325 ≤ 371458093) block2 block3

theorem join_1_0 : (twinPrimeSegment 371327021 371458093).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 371327021 ≤ 371392557)
    (by decide : 371392557 ≤ 371458093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 371327021 371458093).card = 431 := join_1_0

end S177C01
end Sude.GeneratedTwinScan
