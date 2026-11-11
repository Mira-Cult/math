import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19916)) 396623917 396656685 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 396623917 396656685).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19916 396623917 396656685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19917)) 396656685 396689453 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 396656685 396689453).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19917 396656685 396689453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19917)) 396689453 396722221 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 396689453 396722221).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19917 396689453 396722221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19918)) 396722221 396754989 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 396722221 396754989).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19918 396722221 396754989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 396623917 396689453).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 396623917 ≤ 396656685)
    (by decide : 396656685 ≤ 396689453) block0 block1

theorem join_0_1 : (twinPrimeSegment 396689453 396754989).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 396689453 ≤ 396722221)
    (by decide : 396722221 ≤ 396754989) block2 block3

theorem join_1_0 : (twinPrimeSegment 396623917 396754989).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 396623917 ≤ 396689453)
    (by decide : 396689453 ≤ 396754989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 396623917 396754989).card = 413 := join_1_0

end S189C02
end Sude.GeneratedTwinScan
