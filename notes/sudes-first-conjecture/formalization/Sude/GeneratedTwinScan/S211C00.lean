import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21036)) 442499117 442531885 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 442499117 442531885).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21036 442499117 442531885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21037)) 442531885 442564653 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 442531885 442564653).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21037 442531885 442564653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21037)) 442564653 442597421 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 442564653 442597421).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21037 442564653 442597421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21038)) 442597421 442630189 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 442597421 442630189).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21038 442597421 442630189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 442499117 442564653).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 442499117 ≤ 442531885)
    (by decide : 442531885 ≤ 442564653) block0 block1

theorem join_0_1 : (twinPrimeSegment 442564653 442630189).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 442564653 ≤ 442597421)
    (by decide : 442597421 ≤ 442630189) block2 block3

theorem join_1_0 : (twinPrimeSegment 442499117 442630189).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 442499117 ≤ 442564653)
    (by decide : 442564653 ≤ 442630189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 442499117 442630189).card = 425 := join_1_0

end S211C00
end Sude.GeneratedTwinScan
