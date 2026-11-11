import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15577)) 242614317 242647085 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 242614317 242647085).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15577 242614317 242647085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15578)) 242647085 242679853 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 242647085 242679853).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15578 242647085 242679853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15579)) 242679853 242712621 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 242679853 242712621).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15579 242679853 242712621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15580)) 242712621 242745389 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 242712621 242745389).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15580 242712621 242745389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 242614317 242679853).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 242614317 ≤ 242647085)
    (by decide : 242647085 ≤ 242679853) block0 block1

theorem join_0_1 : (twinPrimeSegment 242679853 242745389).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 242679853 ≤ 242712621)
    (by decide : 242712621 ≤ 242745389) block2 block3

theorem join_1_0 : (twinPrimeSegment 242614317 242745389).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 242614317 ≤ 242679853)
    (by decide : 242679853 ≤ 242745389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 242614317 242745389).card = 455 := join_1_0

end S115C11
end Sude.GeneratedTwinScan
