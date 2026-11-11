import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22138)) 490078253 490111021 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 490078253 490111021).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22138 490078253 490111021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22139)) 490111021 490143789 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 490111021 490143789).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22139 490111021 490143789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22139)) 490143789 490176557 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 490143789 490176557).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22139 490143789 490176557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22140)) 490176557 490209325 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 490176557 490209325).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22140 490176557 490209325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 490078253 490143789).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 490078253 ≤ 490111021)
    (by decide : 490111021 ≤ 490143789) block0 block1

theorem join_0_1 : (twinPrimeSegment 490143789 490209325).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 490143789 ≤ 490176557)
    (by decide : 490176557 ≤ 490209325) block2 block3

theorem join_1_0 : (twinPrimeSegment 490078253 490209325).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 490078253 ≤ 490143789)
    (by decide : 490143789 ≤ 490209325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 490078253 490209325).card = 412 := join_1_0

end S233C11
end Sude.GeneratedTwinScan
