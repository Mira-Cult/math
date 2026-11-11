import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17964)) 322699309 322732077 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 322699309 322732077).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17964 322699309 322732077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17965)) 322732077 322764845 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 322732077 322764845).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17965 322732077 322764845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17966)) 322764845 322797613 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 322764845 322797613).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17966 322764845 322797613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17967)) 322797613 322830381 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 322797613 322830381).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17967 322797613 322830381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 322699309 322764845).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 322699309 ≤ 322732077)
    (by decide : 322732077 ≤ 322764845) block0 block1

theorem join_0_1 : (twinPrimeSegment 322764845 322830381).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 322764845 ≤ 322797613)
    (by decide : 322797613 ≤ 322830381) block2 block3

theorem join_1_0 : (twinPrimeSegment 322699309 322830381).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 322699309 ≤ 322764845)
    (by decide : 322764845 ≤ 322830381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 322699309 322830381).card = 450 := join_1_0

end S153C14
end Sude.GeneratedTwinScan
