import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21532)) 463601709 463634477 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 463601709 463634477).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21532 463601709 463634477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21532)) 463634477 463667245 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 463634477 463667245).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21532 463634477 463667245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21533)) 463667245 463700013 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 463667245 463700013).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21533 463667245 463700013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21534)) 463700013 463732781 = 85 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 463700013 463732781).card = 85 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21534 463700013 463732781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 463601709 463667245).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 463601709 ≤ 463634477)
    (by decide : 463634477 ≤ 463667245) block0 block1

theorem join_0_1 : (twinPrimeSegment 463667245 463732781).card = 177 := by
  simpa using combineTwinPrimeSegments (by decide : 463667245 ≤ 463700013)
    (by decide : 463700013 ≤ 463732781) block2 block3

theorem join_1_0 : (twinPrimeSegment 463601709 463732781).card = 389 := by
  simpa using combineTwinPrimeSegments (by decide : 463601709 ≤ 463667245)
    (by decide : 463667245 ≤ 463732781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 463601709 463732781).card = 389 := join_1_0

end S221C01
end Sude.GeneratedTwinScan
