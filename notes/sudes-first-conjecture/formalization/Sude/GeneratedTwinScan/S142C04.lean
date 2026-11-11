import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17272)) 298319917 298352685 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 298319917 298352685).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17272 298319917 298352685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17273)) 298352685 298385453 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 298352685 298385453).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17273 298352685 298385453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17274)) 298385453 298418221 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 298385453 298418221).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17274 298385453 298418221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17275)) 298418221 298450989 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 298418221 298450989).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17275 298418221 298450989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 298319917 298385453).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 298319917 ≤ 298352685)
    (by decide : 298352685 ≤ 298385453) block0 block1

theorem join_0_1 : (twinPrimeSegment 298385453 298450989).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 298385453 ≤ 298418221)
    (by decide : 298418221 ≤ 298450989) block2 block3

theorem join_1_0 : (twinPrimeSegment 298319917 298450989).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 298319917 ≤ 298385453)
    (by decide : 298385453 ≤ 298450989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 298319917 298450989).card = 471 := join_1_0

end S142C04
end Sude.GeneratedTwinScan
