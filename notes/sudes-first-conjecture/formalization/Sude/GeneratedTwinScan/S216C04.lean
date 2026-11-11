import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21296)) 453509165 453541933 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 453509165 453541933).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21296 453509165 453541933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21297)) 453541933 453574701 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 453541933 453574701).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21297 453541933 453574701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21298)) 453574701 453607469 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 453574701 453607469).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21298 453574701 453607469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21298)) 453607469 453640237 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 453607469 453640237).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21298 453607469 453640237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 453509165 453574701).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 453509165 ≤ 453541933)
    (by decide : 453541933 ≤ 453574701) block0 block1

theorem join_0_1 : (twinPrimeSegment 453574701 453640237).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 453574701 ≤ 453607469)
    (by decide : 453607469 ≤ 453640237) block2 block3

theorem join_1_0 : (twinPrimeSegment 453509165 453640237).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 453509165 ≤ 453574701)
    (by decide : 453574701 ≤ 453640237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 453509165 453640237).card = 432 := join_1_0

end S216C04
end Sude.GeneratedTwinScan
