import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14568)) 212205613 212238381 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 212205613 212238381).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14568 212205613 212238381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14569)) 212238381 212271149 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 212238381 212271149).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14569 212238381 212271149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14570)) 212271149 212303917 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 212271149 212303917).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14570 212271149 212303917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14571)) 212303917 212336685 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 212303917 212336685).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14571 212303917 212336685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 212205613 212271149).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 212205613 ≤ 212238381)
    (by decide : 212238381 ≤ 212271149) block0 block1

theorem join_0_1 : (twinPrimeSegment 212271149 212336685).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 212271149 ≤ 212303917)
    (by decide : 212303917 ≤ 212336685) block2 block3

theorem join_1_0 : (twinPrimeSegment 212205613 212336685).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 212205613 ≤ 212271149)
    (by decide : 212271149 ≤ 212336685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 212205613 212336685).card = 454 := join_1_0

end S101C03
end Sude.GeneratedTwinScan
