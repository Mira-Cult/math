import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18464)) 340918317 340951085 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 340918317 340951085).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18464 340918317 340951085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18465)) 340951085 340983853 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 340951085 340983853).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18465 340951085 340983853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18466)) 340983853 341016621 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 340983853 341016621).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18466 340983853 341016621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18467)) 341016621 341049389 = 84 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 341016621 341049389).card = 84 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18467 341016621 341049389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 340918317 340983853).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 340918317 ≤ 340951085)
    (by decide : 340951085 ≤ 340983853) block0 block1

theorem join_0_1 : (twinPrimeSegment 340983853 341049389).card = 188 := by
  simpa using combineTwinPrimeSegments (by decide : 340983853 ≤ 341016621)
    (by decide : 341016621 ≤ 341049389) block2 block3

theorem join_1_0 : (twinPrimeSegment 340918317 341049389).card = 402 := by
  simpa using combineTwinPrimeSegments (by decide : 340918317 ≤ 340983853)
    (by decide : 340983853 ≤ 341049389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 340918317 341049389).card = 402 := join_1_0

end S162C09
end Sude.GeneratedTwinScan
