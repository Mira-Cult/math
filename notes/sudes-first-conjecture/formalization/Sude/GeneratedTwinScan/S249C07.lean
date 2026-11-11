import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22872)) 523108397 523141165 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 523108397 523141165).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22872 523108397 523141165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22872)) 523141165 523173933 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 523141165 523173933).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22872 523141165 523173933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22873)) 523173933 523206701 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 523173933 523206701).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22873 523173933 523206701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22874)) 523206701 523239469 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 523206701 523239469).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22874 523206701 523239469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 523108397 523173933).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 523108397 ≤ 523141165)
    (by decide : 523141165 ≤ 523173933) block0 block1

theorem join_0_1 : (twinPrimeSegment 523173933 523239469).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 523173933 ≤ 523206701)
    (by decide : 523206701 ≤ 523239469) block2 block3

theorem join_1_0 : (twinPrimeSegment 523108397 523239469).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 523108397 ≤ 523173933)
    (by decide : 523173933 ≤ 523239469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 523108397 523239469).card = 462 := join_1_0

end S249C07
end Sude.GeneratedTwinScan
