import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21357)) 456130605 456163373 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 456130605 456163373).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21357 456130605 456163373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21358)) 456163373 456196141 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 456163373 456196141).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21358 456163373 456196141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21359)) 456196141 456228909 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 456196141 456228909).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21359 456196141 456228909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21360)) 456228909 456261677 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 456228909 456261677).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21360 456228909 456261677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 456130605 456196141).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 456130605 ≤ 456163373)
    (by decide : 456163373 ≤ 456196141) block0 block1

theorem join_0_1 : (twinPrimeSegment 456196141 456261677).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 456196141 ≤ 456228909)
    (by decide : 456228909 ≤ 456261677) block2 block3

theorem join_1_0 : (twinPrimeSegment 456130605 456261677).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 456130605 ≤ 456196141)
    (by decide : 456196141 ≤ 456261677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 456130605 456261677).card = 421 := join_1_0

end S217C08
end Sude.GeneratedTwinScan
