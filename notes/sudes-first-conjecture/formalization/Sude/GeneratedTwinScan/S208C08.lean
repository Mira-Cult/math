import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20911)) 437256237 437289005 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 437256237 437289005).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20911 437256237 437289005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20912)) 437289005 437321773 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 437289005 437321773).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20912 437289005 437321773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20913)) 437321773 437354541 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 437321773 437354541).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20913 437321773 437354541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20913)) 437354541 437387309 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 437354541 437387309).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20913 437354541 437387309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 437256237 437321773).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 437256237 ≤ 437289005)
    (by decide : 437289005 ≤ 437321773) block0 block1

theorem join_0_1 : (twinPrimeSegment 437321773 437387309).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 437321773 ≤ 437354541)
    (by decide : 437354541 ≤ 437387309) block2 block3

theorem join_1_0 : (twinPrimeSegment 437256237 437387309).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 437256237 ≤ 437321773)
    (by decide : 437321773 ≤ 437387309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 437256237 437387309).card = 436 := join_1_0

end S208C08
end Sude.GeneratedTwinScan
