import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12527)) 156893229 156925997 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 156893229 156925997).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12527 156893229 156925997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12528)) 156925997 156958765 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 156925997 156958765).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12528 156925997 156958765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12529)) 156958765 156991533 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 156958765 156991533).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12529 156958765 156991533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12530)) 156991533 157024301 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 156991533 157024301).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12530 156991533 157024301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 156893229 156958765).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 156893229 ≤ 156925997)
    (by decide : 156925997 ≤ 156958765) block0 block1

theorem join_0_1 : (twinPrimeSegment 156958765 157024301).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 156958765 ≤ 156991533)
    (by decide : 156991533 ≤ 157024301) block2 block3

theorem join_1_0 : (twinPrimeSegment 156893229 157024301).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 156893229 ≤ 156958765)
    (by decide : 156958765 ≤ 157024301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 156893229 157024301).card = 460 := join_1_0

end S074C13
end Sude.GeneratedTwinScan
