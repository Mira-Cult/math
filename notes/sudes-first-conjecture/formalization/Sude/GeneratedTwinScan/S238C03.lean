import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22350)) 499515437 499548205 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 499515437 499548205).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22350 499515437 499548205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22351)) 499548205 499580973 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 499548205 499580973).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22351 499548205 499580973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22352)) 499580973 499613741 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 499580973 499613741).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22352 499580973 499613741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22352)) 499613741 499646509 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 499613741 499646509).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22352 499613741 499646509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 499515437 499580973).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 499515437 ≤ 499548205)
    (by decide : 499548205 ≤ 499580973) block0 block1

theorem join_0_1 : (twinPrimeSegment 499580973 499646509).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 499580973 ≤ 499613741)
    (by decide : 499613741 ≤ 499646509) block2 block3

theorem join_1_0 : (twinPrimeSegment 499515437 499646509).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 499515437 ≤ 499580973)
    (by decide : 499580973 ≤ 499646509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 499515437 499646509).card = 436 := join_1_0

end S238C03
end Sude.GeneratedTwinScan
