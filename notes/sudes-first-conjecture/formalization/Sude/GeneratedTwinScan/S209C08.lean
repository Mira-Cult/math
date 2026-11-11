import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20961)) 439353389 439386157 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 439353389 439386157).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20961 439353389 439386157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20962)) 439386157 439418925 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 439386157 439418925).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20962 439386157 439418925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20963)) 439418925 439451693 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 439418925 439451693).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20963 439418925 439451693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20963)) 439451693 439484461 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 439451693 439484461).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20963 439451693 439484461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 439353389 439418925).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 439353389 ≤ 439386157)
    (by decide : 439386157 ≤ 439418925) block0 block1

theorem join_0_1 : (twinPrimeSegment 439418925 439484461).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 439418925 ≤ 439451693)
    (by decide : 439451693 ≤ 439484461) block2 block3

theorem join_1_0 : (twinPrimeSegment 439353389 439484461).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 439353389 ≤ 439418925)
    (by decide : 439418925 ≤ 439484461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 439353389 439484461).card = 438 := join_1_0

end S209C08
end Sude.GeneratedTwinScan
