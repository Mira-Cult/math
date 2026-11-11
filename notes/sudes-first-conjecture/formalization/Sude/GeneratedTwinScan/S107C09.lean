import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15020)) 225574957 225607725 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 225574957 225607725).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15020 225574957 225607725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15021)) 225607725 225640493 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 225607725 225640493).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15021 225607725 225640493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15022)) 225640493 225673261 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 225640493 225673261).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15022 225640493 225673261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15023)) 225673261 225706029 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 225673261 225706029).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15023 225673261 225706029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 225574957 225640493).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 225574957 ≤ 225607725)
    (by decide : 225607725 ≤ 225640493) block0 block1

theorem join_0_1 : (twinPrimeSegment 225640493 225706029).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 225640493 ≤ 225673261)
    (by decide : 225673261 ≤ 225706029) block2 block3

theorem join_1_0 : (twinPrimeSegment 225574957 225706029).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 225574957 ≤ 225640493)
    (by decide : 225640493 ≤ 225706029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 225574957 225706029).card = 441 := join_1_0

end S107C09
end Sude.GeneratedTwinScan
