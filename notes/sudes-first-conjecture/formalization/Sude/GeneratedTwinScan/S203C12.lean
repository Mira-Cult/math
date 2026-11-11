import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20671)) 427294765 427327533 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 427294765 427327533).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20671 427294765 427327533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20672)) 427327533 427360301 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 427327533 427360301).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20672 427327533 427360301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20673)) 427360301 427393069 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 427360301 427393069).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20673 427360301 427393069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20674)) 427393069 427425837 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 427393069 427425837).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20674 427393069 427425837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 427294765 427360301).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 427294765 ≤ 427327533)
    (by decide : 427327533 ≤ 427360301) block0 block1

theorem join_0_1 : (twinPrimeSegment 427360301 427425837).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 427360301 ≤ 427393069)
    (by decide : 427393069 ≤ 427425837) block2 block3

theorem join_1_0 : (twinPrimeSegment 427294765 427425837).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 427294765 ≤ 427360301)
    (by decide : 427360301 ≤ 427425837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 427294765 427425837).card = 439 := join_1_0

end S203C12
end Sude.GeneratedTwinScan
