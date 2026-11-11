import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16599)) 275513389 275546157 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 275513389 275546157).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16599 275513389 275546157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16600)) 275546157 275578925 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 275546157 275578925).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16600 275546157 275578925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16601)) 275578925 275611693 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 275578925 275611693).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16601 275578925 275611693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16602)) 275611693 275644461 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 275611693 275644461).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16602 275611693 275644461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 275513389 275578925).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 275513389 ≤ 275546157)
    (by decide : 275546157 ≤ 275578925) block0 block1

theorem join_0_1 : (twinPrimeSegment 275578925 275644461).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 275578925 ≤ 275611693)
    (by decide : 275611693 ≤ 275644461) block2 block3

theorem join_1_0 : (twinPrimeSegment 275513389 275644461).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 275513389 ≤ 275578925)
    (by decide : 275578925 ≤ 275644461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 275513389 275644461).card = 430 := join_1_0

end S131C06
end Sude.GeneratedTwinScan
