import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17979)) 323223597 323256365 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 323223597 323256365).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17979 323223597 323256365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17980)) 323256365 323289133 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 323256365 323289133).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17980 323256365 323289133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17981)) 323289133 323321901 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 323289133 323321901).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17981 323289133 323321901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17982)) 323321901 323354669 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 323321901 323354669).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17982 323321901 323354669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 323223597 323289133).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 323223597 ≤ 323256365)
    (by decide : 323256365 ≤ 323289133) block0 block1

theorem join_0_1 : (twinPrimeSegment 323289133 323354669).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 323289133 ≤ 323321901)
    (by decide : 323321901 ≤ 323354669) block2 block3

theorem join_1_0 : (twinPrimeSegment 323223597 323354669).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 323223597 ≤ 323289133)
    (by decide : 323289133 ≤ 323354669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 323223597 323354669).card = 471 := join_1_0

end S154C02
end Sude.GeneratedTwinScan
