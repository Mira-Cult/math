import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14259)) 203292717 203325485 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 203292717 203325485).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14259 203292717 203325485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14260)) 203325485 203358253 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 203325485 203358253).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14260 203325485 203358253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14261)) 203358253 203391021 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 203358253 203391021).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14261 203358253 203391021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14262)) 203391021 203423789 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 203391021 203423789).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14262 203391021 203423789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 203292717 203358253).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 203292717 ≤ 203325485)
    (by decide : 203325485 ≤ 203358253) block0 block1

theorem join_0_1 : (twinPrimeSegment 203358253 203423789).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 203358253 ≤ 203391021)
    (by decide : 203391021 ≤ 203423789) block2 block3

theorem join_1_0 : (twinPrimeSegment 203292717 203423789).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 203292717 ≤ 203358253)
    (by decide : 203358253 ≤ 203423789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 203292717 203423789).card = 486 := join_1_0

end S096C15
end Sude.GeneratedTwinScan
