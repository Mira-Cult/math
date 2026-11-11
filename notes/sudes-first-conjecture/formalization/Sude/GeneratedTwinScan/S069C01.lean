import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144834605 144867373 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 144834605 144867373).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144834605 144867373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144867373 144900141 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 144867373 144900141).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144867373 144900141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144900141 144932909 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 144900141 144932909).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144900141 144932909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144932909 144965677 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 144932909 144965677).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144932909 144965677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 144834605 144900141).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 144834605 ≤ 144867373)
    (by decide : 144867373 ≤ 144900141) block0 block1

theorem join_0_1 : (twinPrimeSegment 144900141 144965677).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 144900141 ≤ 144932909)
    (by decide : 144932909 ≤ 144965677) block2 block3

theorem join_1_0 : (twinPrimeSegment 144834605 144965677).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 144834605 ≤ 144900141)
    (by decide : 144900141 ≤ 144965677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 144834605 144965677).card = 464 := join_1_0

end S069C01
end Sude.GeneratedTwinScan
