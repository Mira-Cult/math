import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102760493 102793261 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 102760493 102793261).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102760493 102793261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102793261 102826029 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 102793261 102826029).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102793261 102826029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102826029 102858797 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 102826029 102858797).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102826029 102858797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102858797 102891565 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 102858797 102891565).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102858797 102891565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 102760493 102826029).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 102760493 ≤ 102793261)
    (by decide : 102793261 ≤ 102826029) block0 block1

theorem join_0_1 : (twinPrimeSegment 102826029 102891565).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 102826029 ≤ 102858797)
    (by decide : 102858797 ≤ 102891565) block2 block3

theorem join_1_0 : (twinPrimeSegment 102760493 102891565).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 102760493 ≤ 102826029)
    (by decide : 102826029 ≤ 102891565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 102760493 102891565).card = 517 := join_1_0

end S049C00
end Sude.GeneratedTwinScan
