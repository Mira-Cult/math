import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19896)) 395837485 395870253 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 395837485 395870253).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19896 395837485 395870253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19897)) 395870253 395903021 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 395870253 395903021).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19897 395870253 395903021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19898)) 395903021 395935789 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 395903021 395935789).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19898 395903021 395935789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19898)) 395935789 395968557 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 395935789 395968557).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19898 395935789 395968557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 395837485 395903021).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 395837485 ≤ 395870253)
    (by decide : 395870253 ≤ 395903021) block0 block1

theorem join_0_1 : (twinPrimeSegment 395903021 395968557).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 395903021 ≤ 395935789)
    (by decide : 395935789 ≤ 395968557) block2 block3

theorem join_1_0 : (twinPrimeSegment 395837485 395968557).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 395837485 ≤ 395903021)
    (by decide : 395903021 ≤ 395968557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 395837485 395968557).card = 460 := join_1_0

end S188C12
end Sude.GeneratedTwinScan
