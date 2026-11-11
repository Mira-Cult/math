import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12427)) 154402861 154435629 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 154402861 154435629).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12427 154402861 154435629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12428)) 154435629 154468397 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 154435629 154468397).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12428 154435629 154468397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12429)) 154468397 154501165 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 154468397 154501165).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12429 154468397 154501165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12431)) 154501165 154533933 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 154501165 154533933).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12431 154501165 154533933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 154402861 154468397).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 154402861 ≤ 154435629)
    (by decide : 154435629 ≤ 154468397) block0 block1

theorem join_0_1 : (twinPrimeSegment 154468397 154533933).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 154468397 ≤ 154501165)
    (by decide : 154501165 ≤ 154533933) block2 block3

theorem join_1_0 : (twinPrimeSegment 154402861 154533933).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 154402861 ≤ 154468397)
    (by decide : 154468397 ≤ 154533933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 154402861 154533933).card = 433 := join_1_0

end S073C10
end Sude.GeneratedTwinScan
