import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17012)) 289407021 289439789 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 289407021 289439789).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17012 289407021 289439789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17013)) 289439789 289472557 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 289439789 289472557).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17013 289439789 289472557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17014)) 289472557 289505325 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 289472557 289505325).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17014 289472557 289505325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17015)) 289505325 289538093 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 289505325 289538093).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17015 289505325 289538093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 289407021 289472557).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 289407021 ≤ 289439789)
    (by decide : 289439789 ≤ 289472557) block0 block1

theorem join_0_1 : (twinPrimeSegment 289472557 289538093).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 289472557 ≤ 289505325)
    (by decide : 289505325 ≤ 289538093) block2 block3

theorem join_1_0 : (twinPrimeSegment 289407021 289538093).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 289407021 ≤ 289472557)
    (by decide : 289472557 ≤ 289538093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 289407021 289538093).card = 475 := join_1_0

end S138C00
end Sude.GeneratedTwinScan
