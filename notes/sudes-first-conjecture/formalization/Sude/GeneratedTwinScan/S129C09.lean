import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16484)) 271712301 271745069 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 271712301 271745069).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16484 271712301 271745069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16485)) 271745069 271777837 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 271745069 271777837).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16485 271745069 271777837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16486)) 271777837 271810605 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 271777837 271810605).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16486 271777837 271810605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16487)) 271810605 271843373 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 271810605 271843373).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16487 271810605 271843373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 271712301 271777837).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 271712301 ≤ 271745069)
    (by decide : 271745069 ≤ 271777837) block0 block1

theorem join_0_1 : (twinPrimeSegment 271777837 271843373).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 271777837 ≤ 271810605)
    (by decide : 271810605 ≤ 271843373) block2 block3

theorem join_1_0 : (twinPrimeSegment 271712301 271843373).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 271712301 ≤ 271777837)
    (by decide : 271777837 ≤ 271843373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 271712301 271843373).card = 435 := join_1_0

end S129C09
end Sude.GeneratedTwinScan
