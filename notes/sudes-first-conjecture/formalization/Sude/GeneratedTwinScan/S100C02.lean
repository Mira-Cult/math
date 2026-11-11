import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14491)) 209977389 210010157 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 209977389 210010157).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14491 209977389 210010157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14492)) 210010157 210042925 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 210010157 210042925).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14492 210010157 210042925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14493)) 210042925 210075693 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 210042925 210075693).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14493 210042925 210075693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14495)) 210075693 210108461 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 210075693 210108461).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14495 210075693 210108461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 209977389 210042925).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 209977389 ≤ 210010157)
    (by decide : 210010157 ≤ 210042925) block0 block1

theorem join_0_1 : (twinPrimeSegment 210042925 210108461).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 210042925 ≤ 210075693)
    (by decide : 210075693 ≤ 210108461) block2 block3

theorem join_1_0 : (twinPrimeSegment 209977389 210108461).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 209977389 ≤ 210042925)
    (by decide : 210042925 ≤ 210108461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 209977389 210108461).card = 470 := join_1_0

end S100C02
end Sude.GeneratedTwinScan
