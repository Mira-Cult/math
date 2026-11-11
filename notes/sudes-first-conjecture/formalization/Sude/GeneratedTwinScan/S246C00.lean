import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22714)) 515899437 515932205 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 515899437 515932205).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22714 515899437 515932205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22714)) 515932205 515964973 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 515932205 515964973).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22714 515932205 515964973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22715)) 515964973 515997741 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 515964973 515997741).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22715 515964973 515997741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22716)) 515997741 516030509 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 515997741 516030509).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22716 515997741 516030509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 515899437 515964973).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 515899437 ≤ 515932205)
    (by decide : 515932205 ≤ 515964973) block0 block1

theorem join_0_1 : (twinPrimeSegment 515964973 516030509).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 515964973 ≤ 515997741)
    (by decide : 515997741 ≤ 516030509) block2 block3

theorem join_1_0 : (twinPrimeSegment 515899437 516030509).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 515899437 ≤ 515964973)
    (by decide : 515964973 ≤ 516030509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 515899437 516030509).card = 433 := join_1_0

end S246C00
end Sude.GeneratedTwinScan
