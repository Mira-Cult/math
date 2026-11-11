import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20958)) 439222317 439255085 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 439222317 439255085).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20958 439222317 439255085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20959)) 439255085 439287853 = 90 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 439255085 439287853).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20959 439255085 439287853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20959)) 439287853 439320621 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 439287853 439320621).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20959 439287853 439320621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20960)) 439320621 439353389 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 439320621 439353389).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20960 439320621 439353389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 439222317 439287853).card = 191 := by
  simpa using combineTwinPrimeSegments (by decide : 439222317 ≤ 439255085)
    (by decide : 439255085 ≤ 439287853) block0 block1

theorem join_0_1 : (twinPrimeSegment 439287853 439353389).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 439287853 ≤ 439320621)
    (by decide : 439320621 ≤ 439353389) block2 block3

theorem join_1_0 : (twinPrimeSegment 439222317 439353389).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 439222317 ≤ 439287853)
    (by decide : 439287853 ≤ 439353389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 439222317 439353389).card = 418 := join_1_0

end S209C07
end Sude.GeneratedTwinScan
