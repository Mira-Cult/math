import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60424237 60457005 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 60424237 60457005).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60424237 60457005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60457005 60489773 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 60457005 60489773).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60457005 60489773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60489773 60522541 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 60489773 60522541).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60489773 60522541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60522541 60555309 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 60522541 60555309).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60522541 60555309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 60424237 60489773).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 60424237 ≤ 60457005)
    (by decide : 60457005 ≤ 60489773) block0 block1

theorem join_0_1 : (twinPrimeSegment 60489773 60555309).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 60489773 ≤ 60522541)
    (by decide : 60522541 ≤ 60555309) block2 block3

theorem join_1_0 : (twinPrimeSegment 60424237 60555309).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 60424237 ≤ 60489773)
    (by decide : 60489773 ≤ 60555309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 60424237 60555309).card = 510 := join_1_0

end S028C13
end Sude.GeneratedTwinScan
