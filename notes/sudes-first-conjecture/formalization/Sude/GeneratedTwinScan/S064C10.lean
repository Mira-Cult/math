import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135528493 135561261 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 135528493 135561261).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135528493 135561261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135561261 135594029 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 135561261 135594029).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135561261 135594029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135594029 135626797 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 135594029 135626797).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135594029 135626797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135626797 135659565 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 135626797 135659565).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135626797 135659565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 135528493 135594029).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 135528493 ≤ 135561261)
    (by decide : 135561261 ≤ 135594029) block0 block1

theorem join_0_1 : (twinPrimeSegment 135594029 135659565).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 135594029 ≤ 135626797)
    (by decide : 135626797 ≤ 135659565) block2 block3

theorem join_1_0 : (twinPrimeSegment 135528493 135659565).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 135528493 ≤ 135594029)
    (by decide : 135594029 ≤ 135659565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 135528493 135659565).card = 477 := join_1_0

end S064C10
end Sude.GeneratedTwinScan
