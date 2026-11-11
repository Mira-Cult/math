import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20474)) 419168301 419201069 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 419168301 419201069).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20474 419168301 419201069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20475)) 419201069 419233837 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 419201069 419233837).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20475 419201069 419233837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20476)) 419233837 419266605 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 419233837 419266605).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20476 419233837 419266605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20476)) 419266605 419299373 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 419266605 419299373).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20476 419266605 419299373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 419168301 419233837).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 419168301 ≤ 419201069)
    (by decide : 419201069 ≤ 419233837) block0 block1

theorem join_0_1 : (twinPrimeSegment 419233837 419299373).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 419233837 ≤ 419266605)
    (by decide : 419266605 ≤ 419299373) block2 block3

theorem join_1_0 : (twinPrimeSegment 419168301 419299373).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 419168301 ≤ 419233837)
    (by decide : 419233837 ≤ 419299373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 419168301 419299373).card = 437 := join_1_0

end S199C14
end Sude.GeneratedTwinScan
