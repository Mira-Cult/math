import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22283)) 496500781 496533549 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 496500781 496533549).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22283 496500781 496533549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22283)) 496533549 496566317 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 496533549 496566317).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22283 496533549 496566317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22284)) 496566317 496599085 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 496566317 496599085).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22284 496566317 496599085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22285)) 496599085 496631853 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 496599085 496631853).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22285 496599085 496631853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 496500781 496566317).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 496500781 ≤ 496533549)
    (by decide : 496533549 ≤ 496566317) block0 block1

theorem join_0_1 : (twinPrimeSegment 496566317 496631853).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 496566317 ≤ 496599085)
    (by decide : 496599085 ≤ 496631853) block2 block3

theorem join_1_0 : (twinPrimeSegment 496500781 496631853).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 496500781 ≤ 496566317)
    (by decide : 496566317 ≤ 496631853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 496500781 496631853).card = 441 := join_1_0

end S236C12
end Sude.GeneratedTwinScan
