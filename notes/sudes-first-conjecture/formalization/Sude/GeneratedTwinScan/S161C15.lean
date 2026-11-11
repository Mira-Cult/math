import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18429)) 339607597 339640365 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 339607597 339640365).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18429 339607597 339640365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18430)) 339640365 339673133 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 339640365 339673133).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18430 339640365 339673133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18431)) 339673133 339705901 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 339673133 339705901).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18431 339673133 339705901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18432)) 339705901 339738669 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 339705901 339738669).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18432 339705901 339738669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 339607597 339673133).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 339607597 ≤ 339640365)
    (by decide : 339640365 ≤ 339673133) block0 block1

theorem join_0_1 : (twinPrimeSegment 339673133 339738669).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 339673133 ≤ 339705901)
    (by decide : 339705901 ≤ 339738669) block2 block3

theorem join_1_0 : (twinPrimeSegment 339607597 339738669).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 339607597 ≤ 339673133)
    (by decide : 339673133 ≤ 339738669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 339607597 339738669).card = 441 := join_1_0

end S161C15
end Sude.GeneratedTwinScan
