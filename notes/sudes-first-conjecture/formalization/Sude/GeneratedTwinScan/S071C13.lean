import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150601773 150634541 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 150601773 150634541).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150601773 150634541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150634541 150667309 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 150634541 150667309).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150634541 150667309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150667309 150700077 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 150667309 150700077).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150667309 150700077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150700077 150732845 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 150700077 150732845).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150700077 150732845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 150601773 150667309).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 150601773 ≤ 150634541)
    (by decide : 150634541 ≤ 150667309) block0 block1

theorem join_0_1 : (twinPrimeSegment 150667309 150732845).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 150667309 ≤ 150700077)
    (by decide : 150700077 ≤ 150732845) block2 block3

theorem join_1_0 : (twinPrimeSegment 150601773 150732845).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 150601773 ≤ 150667309)
    (by decide : 150667309 ≤ 150732845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 150601773 150732845).card = 477 := join_1_0

end S071C13
end Sude.GeneratedTwinScan
