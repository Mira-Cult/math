import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19375)) 375390253 375423021 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 375390253 375423021).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19375 375390253 375423021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19376)) 375423021 375455789 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 375423021 375455789).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19376 375423021 375455789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19377)) 375455789 375488557 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 375455789 375488557).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19377 375455789 375488557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19378)) 375488557 375521325 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 375488557 375521325).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19378 375488557 375521325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 375390253 375455789).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 375390253 ≤ 375423021)
    (by decide : 375423021 ≤ 375455789) block0 block1

theorem join_0_1 : (twinPrimeSegment 375455789 375521325).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 375455789 ≤ 375488557)
    (by decide : 375488557 ≤ 375521325) block2 block3

theorem join_1_0 : (twinPrimeSegment 375390253 375521325).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 375390253 ≤ 375455789)
    (by decide : 375455789 ≤ 375521325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 375390253 375521325).card = 487 := join_1_0

end S179C00
end Sude.GeneratedTwinScan
