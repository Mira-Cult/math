import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22829)) 521142317 521175085 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 521142317 521175085).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22829 521142317 521175085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22829)) 521175085 521207853 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 521175085 521207853).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22829 521175085 521207853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22830)) 521207853 521240621 = 88 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 521207853 521240621).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22830 521207853 521240621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22831)) 521240621 521273389 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 521240621 521273389).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22831 521240621 521273389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 521142317 521207853).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 521142317 ≤ 521175085)
    (by decide : 521175085 ≤ 521207853) block0 block1

theorem join_0_1 : (twinPrimeSegment 521207853 521273389).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 521207853 ≤ 521240621)
    (by decide : 521240621 ≤ 521273389) block2 block3

theorem join_1_0 : (twinPrimeSegment 521142317 521273389).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 521142317 ≤ 521207853)
    (by decide : 521207853 ≤ 521273389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 521142317 521273389).card = 431 := join_1_0

end S248C08
end Sude.GeneratedTwinScan
