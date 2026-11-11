import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20161)) 406454317 406487085 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 406454317 406487085).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20161 406454317 406487085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20162)) 406487085 406519853 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 406487085 406519853).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20162 406487085 406519853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20163)) 406519853 406552621 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 406519853 406552621).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20163 406519853 406552621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20163)) 406552621 406585389 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 406552621 406585389).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20163 406552621 406585389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 406454317 406519853).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 406454317 ≤ 406487085)
    (by decide : 406487085 ≤ 406519853) block0 block1

theorem join_0_1 : (twinPrimeSegment 406519853 406585389).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 406519853 ≤ 406552621)
    (by decide : 406552621 ≤ 406585389) block2 block3

theorem join_1_0 : (twinPrimeSegment 406454317 406585389).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 406454317 ≤ 406519853)
    (by decide : 406519853 ≤ 406585389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 406454317 406585389).card = 430 := join_1_0

end S193C13
end Sude.GeneratedTwinScan
