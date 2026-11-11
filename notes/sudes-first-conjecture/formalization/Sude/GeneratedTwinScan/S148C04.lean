import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17633)) 310902829 310935597 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 310902829 310935597).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17633 310902829 310935597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17634)) 310935597 310968365 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 310935597 310968365).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17634 310935597 310968365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17635)) 310968365 311001133 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 310968365 311001133).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17635 310968365 311001133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17636)) 311001133 311033901 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 311001133 311033901).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17636 311001133 311033901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 310902829 310968365).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 310902829 ≤ 310935597)
    (by decide : 310935597 ≤ 310968365) block0 block1

theorem join_0_1 : (twinPrimeSegment 310968365 311033901).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 310968365 ≤ 311001133)
    (by decide : 311001133 ≤ 311033901) block2 block3

theorem join_1_0 : (twinPrimeSegment 310902829 311033901).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 310902829 ≤ 310968365)
    (by decide : 310968365 ≤ 311033901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 310902829 311033901).card = 493 := join_1_0

end S148C04
end Sude.GeneratedTwinScan
