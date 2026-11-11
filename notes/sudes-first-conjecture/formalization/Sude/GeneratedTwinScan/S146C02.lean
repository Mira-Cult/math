import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17506)) 306446381 306479149 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 306446381 306479149).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17506 306446381 306479149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17507)) 306479149 306511917 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 306479149 306511917).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17507 306479149 306511917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17508)) 306511917 306544685 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 306511917 306544685).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17508 306511917 306544685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17509)) 306544685 306577453 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 306544685 306577453).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17509 306544685 306577453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 306446381 306511917).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 306446381 ≤ 306479149)
    (by decide : 306479149 ≤ 306511917) block0 block1

theorem join_0_1 : (twinPrimeSegment 306511917 306577453).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 306511917 ≤ 306544685)
    (by decide : 306544685 ≤ 306577453) block2 block3

theorem join_1_0 : (twinPrimeSegment 306446381 306577453).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 306446381 ≤ 306511917)
    (by decide : 306511917 ≤ 306577453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 306446381 306577453).card = 461 := join_1_0

end S146C02
end Sude.GeneratedTwinScan
