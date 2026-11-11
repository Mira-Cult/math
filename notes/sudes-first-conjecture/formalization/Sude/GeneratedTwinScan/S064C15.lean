import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136183853 136216621 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 136183853 136216621).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136183853 136216621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136216621 136249389 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 136216621 136249389).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136216621 136249389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136249389 136282157 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 136249389 136282157).card = 107 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136249389 136282157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136282157 136314925 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 136282157 136314925).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136282157 136314925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 136183853 136249389).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 136183853 ≤ 136216621)
    (by decide : 136216621 ≤ 136249389) block0 block1

theorem join_0_1 : (twinPrimeSegment 136249389 136314925).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 136249389 ≤ 136282157)
    (by decide : 136282157 ≤ 136314925) block2 block3

theorem join_1_0 : (twinPrimeSegment 136183853 136314925).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 136183853 ≤ 136249389)
    (by decide : 136249389 ≤ 136314925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 136183853 136314925).card = 487 := join_1_0

end S064C15
end Sude.GeneratedTwinScan
