import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15522)) 240910381 240943149 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 240910381 240943149).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15522 240910381 240943149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15523)) 240943149 240975917 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 240943149 240975917).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15523 240943149 240975917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15524)) 240975917 241008685 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 240975917 241008685).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15524 240975917 241008685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15525)) 241008685 241041453 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 241008685 241041453).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15525 241008685 241041453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 240910381 240975917).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 240910381 ≤ 240943149)
    (by decide : 240943149 ≤ 240975917) block0 block1

theorem join_0_1 : (twinPrimeSegment 240975917 241041453).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 240975917 ≤ 241008685)
    (by decide : 241008685 ≤ 241041453) block2 block3

theorem join_1_0 : (twinPrimeSegment 240910381 241041453).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 240910381 ≤ 240975917)
    (by decide : 240975917 ≤ 241041453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 240910381 241041453).card = 456 := join_1_0

end S114C14
end Sude.GeneratedTwinScan
