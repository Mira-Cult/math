import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21876)) 478543917 478576685 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 478543917 478576685).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21876 478543917 478576685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21877)) 478576685 478609453 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 478576685 478609453).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21877 478576685 478609453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21877)) 478609453 478642221 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 478609453 478642221).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21877 478609453 478642221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21878)) 478642221 478674989 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 478642221 478674989).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21878 478642221 478674989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 478543917 478609453).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 478543917 ≤ 478576685)
    (by decide : 478576685 ≤ 478609453) block0 block1

theorem join_0_1 : (twinPrimeSegment 478609453 478674989).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 478609453 ≤ 478642221)
    (by decide : 478642221 ≤ 478674989) block2 block3

theorem join_1_0 : (twinPrimeSegment 478543917 478674989).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 478543917 ≤ 478609453)
    (by decide : 478609453 ≤ 478674989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 478543917 478674989).card = 468 := join_1_0

end S228C03
end Sude.GeneratedTwinScan
