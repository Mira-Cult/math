import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13896)) 193069101 193101869 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 193069101 193101869).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13896 193069101 193101869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13897)) 193101869 193134637 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 193101869 193134637).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13897 193101869 193134637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13898)) 193134637 193167405 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 193134637 193167405).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13898 193134637 193167405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13899)) 193167405 193200173 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 193167405 193200173).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13899 193167405 193200173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 193069101 193134637).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 193069101 ≤ 193101869)
    (by decide : 193101869 ≤ 193134637) block0 block1

theorem join_0_1 : (twinPrimeSegment 193134637 193200173).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 193134637 ≤ 193167405)
    (by decide : 193167405 ≤ 193200173) block2 block3

theorem join_1_0 : (twinPrimeSegment 193069101 193200173).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 193069101 ≤ 193134637)
    (by decide : 193134637 ≤ 193200173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 193069101 193200173).card = 479 := join_1_0

end S092C01
end Sude.GeneratedTwinScan
