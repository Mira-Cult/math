import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135266349 135299117 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 135266349 135299117).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135266349 135299117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135299117 135331885 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 135299117 135331885).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135299117 135331885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135331885 135364653 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 135331885 135364653).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135331885 135364653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135364653 135397421 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 135364653 135397421).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135364653 135397421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 135266349 135331885).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 135266349 ≤ 135299117)
    (by decide : 135299117 ≤ 135331885) block0 block1

theorem join_0_1 : (twinPrimeSegment 135331885 135397421).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 135331885 ≤ 135364653)
    (by decide : 135364653 ≤ 135397421) block2 block3

theorem join_1_0 : (twinPrimeSegment 135266349 135397421).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 135266349 ≤ 135331885)
    (by decide : 135331885 ≤ 135397421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 135266349 135397421).card = 482 := join_1_0

end S064C08
end Sude.GeneratedTwinScan
