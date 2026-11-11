import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65929261 65962029 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 65929261 65962029).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65929261 65962029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65962029 65994797 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 65962029 65994797).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65962029 65994797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65994797 66027565 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 65994797 66027565).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65994797 66027565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66027565 66060333 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 66027565 66060333).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66027565 66060333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 65929261 65994797).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 65929261 ≤ 65962029)
    (by decide : 65962029 ≤ 65994797) block0 block1

theorem join_0_1 : (twinPrimeSegment 65994797 66060333).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 65994797 ≤ 66027565)
    (by decide : 66027565 ≤ 66060333) block2 block3

theorem join_1_0 : (twinPrimeSegment 65929261 66060333).card = 515 := by
  simpa using combineTwinPrimeSegments (by decide : 65929261 ≤ 65994797)
    (by decide : 65994797 ≤ 66060333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 65929261 66060333).card = 515 := join_1_0

end S031C07
end Sude.GeneratedTwinScan
