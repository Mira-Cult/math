import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17986)) 323485741 323518509 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 323485741 323518509).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17986 323485741 323518509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17987)) 323518509 323551277 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 323518509 323551277).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17987 323518509 323551277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17988)) 323551277 323584045 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 323551277 323584045).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17988 323551277 323584045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17989)) 323584045 323616813 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 323584045 323616813).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17989 323584045 323616813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 323485741 323551277).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 323485741 ≤ 323518509)
    (by decide : 323518509 ≤ 323551277) block0 block1

theorem join_0_1 : (twinPrimeSegment 323551277 323616813).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 323551277 ≤ 323584045)
    (by decide : 323584045 ≤ 323616813) block2 block3

theorem join_1_0 : (twinPrimeSegment 323485741 323616813).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 323485741 ≤ 323551277)
    (by decide : 323551277 ≤ 323616813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 323485741 323616813).card = 470 := join_1_0

end S154C04
end Sude.GeneratedTwinScan
