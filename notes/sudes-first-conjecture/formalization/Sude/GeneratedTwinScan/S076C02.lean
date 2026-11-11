import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12636)) 159645741 159678509 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 159645741 159678509).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12636 159645741 159678509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12637)) 159678509 159711277 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 159678509 159711277).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12637 159678509 159711277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12638)) 159711277 159744045 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 159711277 159744045).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12638 159711277 159744045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12640)) 159744045 159776813 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 159744045 159776813).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12640 159744045 159776813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 159645741 159711277).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 159645741 ≤ 159678509)
    (by decide : 159678509 ≤ 159711277) block0 block1

theorem join_0_1 : (twinPrimeSegment 159711277 159776813).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 159711277 ≤ 159744045)
    (by decide : 159744045 ≤ 159776813) block2 block3

theorem join_1_0 : (twinPrimeSegment 159645741 159776813).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 159645741 ≤ 159711277)
    (by decide : 159711277 ≤ 159776813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 159645741 159776813).card = 473 := join_1_0

end S076C02
end Sude.GeneratedTwinScan
