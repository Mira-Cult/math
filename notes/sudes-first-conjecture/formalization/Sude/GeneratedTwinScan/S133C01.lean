import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16705)) 279052333 279085101 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 279052333 279085101).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16705 279052333 279085101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16706)) 279085101 279117869 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 279085101 279117869).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16706 279085101 279117869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16707)) 279117869 279150637 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 279117869 279150637).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16707 279117869 279150637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16708)) 279150637 279183405 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 279150637 279183405).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16708 279150637 279183405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 279052333 279117869).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 279052333 ≤ 279085101)
    (by decide : 279085101 ≤ 279117869) block0 block1

theorem join_0_1 : (twinPrimeSegment 279117869 279183405).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 279117869 ≤ 279150637)
    (by decide : 279150637 ≤ 279183405) block2 block3

theorem join_1_0 : (twinPrimeSegment 279052333 279183405).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 279052333 ≤ 279117869)
    (by decide : 279117869 ≤ 279183405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 279052333 279183405).card = 480 := join_1_0

end S133C01
end Sude.GeneratedTwinScan
