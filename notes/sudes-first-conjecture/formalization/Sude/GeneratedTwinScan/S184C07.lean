import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19667)) 386793517 386826285 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 386793517 386826285).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19667 386793517 386826285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19668)) 386826285 386859053 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 386826285 386859053).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19668 386826285 386859053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19669)) 386859053 386891821 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 386859053 386891821).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19669 386859053 386891821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19670)) 386891821 386924589 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 386891821 386924589).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19670 386891821 386924589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 386793517 386859053).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 386793517 ≤ 386826285)
    (by decide : 386826285 ≤ 386859053) block0 block1

theorem join_0_1 : (twinPrimeSegment 386859053 386924589).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 386859053 ≤ 386891821)
    (by decide : 386891821 ≤ 386924589) block2 block3

theorem join_1_0 : (twinPrimeSegment 386793517 386924589).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 386793517 ≤ 386859053)
    (by decide : 386859053 ≤ 386924589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 386793517 386924589).card = 451 := join_1_0

end S184C07
end Sude.GeneratedTwinScan
