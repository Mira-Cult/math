import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16908)) 285868077 285900845 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 285868077 285900845).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16908 285868077 285900845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16909)) 285900845 285933613 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 285900845 285933613).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16909 285900845 285933613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16910)) 285933613 285966381 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 285933613 285966381).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16910 285933613 285966381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16911)) 285966381 285999149 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 285966381 285999149).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16911 285966381 285999149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 285868077 285933613).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 285868077 ≤ 285900845)
    (by decide : 285900845 ≤ 285933613) block0 block1

theorem join_0_1 : (twinPrimeSegment 285933613 285999149).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 285933613 ≤ 285966381)
    (by decide : 285966381 ≤ 285999149) block2 block3

theorem join_1_0 : (twinPrimeSegment 285868077 285999149).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 285868077 ≤ 285933613)
    (by decide : 285933613 ≤ 285999149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 285868077 285999149).card = 468 := join_1_0

end S136C05
end Sude.GeneratedTwinScan
