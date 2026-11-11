import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21879)) 478674989 478707757 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 478674989 478707757).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21879 478674989 478707757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21880)) 478707757 478740525 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 478707757 478740525).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21880 478707757 478740525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21880)) 478740525 478773293 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 478740525 478773293).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21880 478740525 478773293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21881)) 478773293 478806061 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 478773293 478806061).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21881 478773293 478806061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 478674989 478740525).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 478674989 ≤ 478707757)
    (by decide : 478707757 ≤ 478740525) block0 block1

theorem join_0_1 : (twinPrimeSegment 478740525 478806061).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 478740525 ≤ 478773293)
    (by decide : 478773293 ≤ 478806061) block2 block3

theorem join_1_0 : (twinPrimeSegment 478674989 478806061).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 478674989 ≤ 478740525)
    (by decide : 478740525 ≤ 478806061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 478674989 478806061).card = 442 := join_1_0

end S228C04
end Sude.GeneratedTwinScan
