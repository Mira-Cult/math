import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21873)) 478412845 478445613 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 478412845 478445613).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21873 478412845 478445613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21874)) 478445613 478478381 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 478445613 478478381).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21874 478445613 478478381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21874)) 478478381 478511149 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 478478381 478511149).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21874 478478381 478511149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21875)) 478511149 478543917 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 478511149 478543917).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21875 478511149 478543917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 478412845 478478381).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 478412845 ≤ 478445613)
    (by decide : 478445613 ≤ 478478381) block0 block1

theorem join_0_1 : (twinPrimeSegment 478478381 478543917).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 478478381 ≤ 478511149)
    (by decide : 478511149 ≤ 478543917) block2 block3

theorem join_1_0 : (twinPrimeSegment 478412845 478543917).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 478412845 ≤ 478478381)
    (by decide : 478478381 ≤ 478543917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 478412845 478543917).card = 415 := join_1_0

end S228C02
end Sude.GeneratedTwinScan
