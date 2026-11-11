import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20760)) 430964781 430997549 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 430964781 430997549).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20760 430964781 430997549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20761)) 430997549 431030317 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 430997549 431030317).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20761 430997549 431030317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20762)) 431030317 431063085 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 431030317 431063085).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20762 431030317 431063085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20762)) 431063085 431095853 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 431063085 431095853).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20762 431063085 431095853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 430964781 431030317).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 430964781 ≤ 430997549)
    (by decide : 430997549 ≤ 431030317) block0 block1

theorem join_0_1 : (twinPrimeSegment 431030317 431095853).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 431030317 ≤ 431063085)
    (by decide : 431063085 ≤ 431095853) block2 block3

theorem join_1_0 : (twinPrimeSegment 430964781 431095853).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 430964781 ≤ 431030317)
    (by decide : 431030317 ≤ 431095853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 430964781 431095853).card = 432 := join_1_0

end S205C08
end Sude.GeneratedTwinScan
