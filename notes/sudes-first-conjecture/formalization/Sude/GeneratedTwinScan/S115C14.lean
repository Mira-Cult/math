import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15589)) 243007533 243040301 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 243007533 243040301).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15589 243007533 243040301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15590)) 243040301 243073069 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 243040301 243073069).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15590 243040301 243073069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15591)) 243073069 243105837 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 243073069 243105837).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15591 243073069 243105837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15592)) 243105837 243138605 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 243105837 243138605).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15592 243105837 243138605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 243007533 243073069).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 243007533 ≤ 243040301)
    (by decide : 243040301 ≤ 243073069) block0 block1

theorem join_0_1 : (twinPrimeSegment 243073069 243138605).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 243073069 ≤ 243105837)
    (by decide : 243105837 ≤ 243138605) block2 block3

theorem join_1_0 : (twinPrimeSegment 243007533 243138605).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 243007533 ≤ 243073069)
    (by decide : 243073069 ≤ 243138605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 243007533 243138605).card = 461 := join_1_0

end S115C14
end Sude.GeneratedTwinScan
