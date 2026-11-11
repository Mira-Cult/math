import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15581)) 242745389 242778157 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 242745389 242778157).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15581 242745389 242778157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15582)) 242778157 242810925 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 242778157 242810925).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15582 242778157 242810925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15583)) 242810925 242843693 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 242810925 242843693).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15583 242810925 242843693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15584)) 242843693 242876461 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 242843693 242876461).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15584 242843693 242876461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 242745389 242810925).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 242745389 ≤ 242778157)
    (by decide : 242778157 ≤ 242810925) block0 block1

theorem join_0_1 : (twinPrimeSegment 242810925 242876461).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 242810925 ≤ 242843693)
    (by decide : 242843693 ≤ 242876461) block2 block3

theorem join_1_0 : (twinPrimeSegment 242745389 242876461).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 242745389 ≤ 242810925)
    (by decide : 242810925 ≤ 242876461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 242745389 242876461).card = 458 := join_1_0

end S115C12
end Sude.GeneratedTwinScan
