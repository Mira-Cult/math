import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15176)) 230293549 230326317 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 230293549 230326317).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15176 230293549 230326317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15177)) 230326317 230359085 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 230326317 230359085).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15177 230326317 230359085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15178)) 230359085 230391853 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 230359085 230391853).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15178 230359085 230391853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15179)) 230391853 230424621 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 230391853 230424621).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15179 230391853 230424621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 230293549 230359085).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 230293549 ≤ 230326317)
    (by decide : 230326317 ≤ 230359085) block0 block1

theorem join_0_1 : (twinPrimeSegment 230359085 230424621).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 230359085 ≤ 230391853)
    (by decide : 230391853 ≤ 230424621) block2 block3

theorem join_1_0 : (twinPrimeSegment 230293549 230424621).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 230293549 ≤ 230359085)
    (by decide : 230359085 ≤ 230424621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 230293549 230424621).card = 485 := join_1_0

end S109C13
end Sude.GeneratedTwinScan
