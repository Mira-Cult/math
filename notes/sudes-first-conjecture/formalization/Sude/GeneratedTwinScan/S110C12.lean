import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15241)) 232259629 232292397 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 232259629 232292397).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15241 232259629 232292397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15242)) 232292397 232325165 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 232292397 232325165).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15242 232292397 232325165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15243)) 232325165 232357933 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 232325165 232357933).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15243 232325165 232357933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15244)) 232357933 232390701 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 232357933 232390701).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15244 232357933 232390701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 232259629 232325165).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 232259629 ≤ 232292397)
    (by decide : 232292397 ≤ 232325165) block0 block1

theorem join_0_1 : (twinPrimeSegment 232325165 232390701).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 232325165 ≤ 232357933)
    (by decide : 232357933 ≤ 232390701) block2 block3

theorem join_1_0 : (twinPrimeSegment 232259629 232390701).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 232259629 ≤ 232325165)
    (by decide : 232325165 ≤ 232390701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 232259629 232390701).card = 456 := join_1_0

end S110C12
end Sude.GeneratedTwinScan
