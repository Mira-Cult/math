import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16904)) 285737005 285769773 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 285737005 285769773).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16904 285737005 285769773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16905)) 285769773 285802541 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 285769773 285802541).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16905 285769773 285802541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16906)) 285802541 285835309 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 285802541 285835309).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16906 285802541 285835309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16907)) 285835309 285868077 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 285835309 285868077).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16907 285835309 285868077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 285737005 285802541).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 285737005 ≤ 285769773)
    (by decide : 285769773 ≤ 285802541) block0 block1

theorem join_0_1 : (twinPrimeSegment 285802541 285868077).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 285802541 ≤ 285835309)
    (by decide : 285835309 ≤ 285868077) block2 block3

theorem join_1_0 : (twinPrimeSegment 285737005 285868077).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 285737005 ≤ 285802541)
    (by decide : 285802541 ≤ 285868077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 285737005 285868077).card = 453 := join_1_0

end S136C04
end Sude.GeneratedTwinScan
