import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19416)) 376963117 376995885 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 376963117 376995885).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19416 376963117 376995885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19417)) 376995885 377028653 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 376995885 377028653).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19417 376995885 377028653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19418)) 377028653 377061421 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 377028653 377061421).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19418 377028653 377061421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19418)) 377061421 377094189 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 377061421 377094189).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19418 377061421 377094189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 376963117 377028653).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 376963117 ≤ 376995885)
    (by decide : 376995885 ≤ 377028653) block0 block1

theorem join_0_1 : (twinPrimeSegment 377028653 377094189).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 377028653 ≤ 377061421)
    (by decide : 377061421 ≤ 377094189) block2 block3

theorem join_1_0 : (twinPrimeSegment 376963117 377094189).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 376963117 ≤ 377028653)
    (by decide : 377028653 ≤ 377094189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 376963117 377094189).card = 450 := join_1_0

end S179C12
end Sude.GeneratedTwinScan
