import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20757)) 430833709 430866477 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 430833709 430866477).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20757 430833709 430866477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20758)) 430866477 430899245 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 430866477 430899245).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20758 430866477 430899245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20758)) 430899245 430932013 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 430899245 430932013).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20758 430899245 430932013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20759)) 430932013 430964781 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 430932013 430964781).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20759 430932013 430964781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 430833709 430899245).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 430833709 ≤ 430866477)
    (by decide : 430866477 ≤ 430899245) block0 block1

theorem join_0_1 : (twinPrimeSegment 430899245 430964781).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 430899245 ≤ 430932013)
    (by decide : 430932013 ≤ 430964781) block2 block3

theorem join_1_0 : (twinPrimeSegment 430833709 430964781).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 430833709 ≤ 430899245)
    (by decide : 430899245 ≤ 430964781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 430833709 430964781).card = 453 := join_1_0

end S205C07
end Sude.GeneratedTwinScan
