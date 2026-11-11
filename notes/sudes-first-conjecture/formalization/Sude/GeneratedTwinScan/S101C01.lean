import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14559)) 211943469 211976237 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 211943469 211976237).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14559 211943469 211976237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14560)) 211976237 212009005 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 211976237 212009005).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14560 211976237 212009005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14561)) 212009005 212041773 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 212009005 212041773).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14561 212009005 212041773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14562)) 212041773 212074541 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 212041773 212074541).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14562 212041773 212074541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 211943469 212009005).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 211943469 ≤ 211976237)
    (by decide : 211976237 ≤ 212009005) block0 block1

theorem join_0_1 : (twinPrimeSegment 212009005 212074541).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 212009005 ≤ 212041773)
    (by decide : 212041773 ≤ 212074541) block2 block3

theorem join_1_0 : (twinPrimeSegment 211943469 212074541).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 211943469 ≤ 212009005)
    (by decide : 212009005 ≤ 212074541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 211943469 212074541).card = 511 := join_1_0

end S101C01
end Sude.GeneratedTwinScan
