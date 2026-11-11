import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104857645 104890413 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 104857645 104890413).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104857645 104890413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104890413 104923181 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 104890413 104923181).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104890413 104923181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104923181 104955949 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 104923181 104955949).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104923181 104955949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104955949 104988717 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 104955949 104988717).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104955949 104988717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 104857645 104923181).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 104857645 ≤ 104890413)
    (by decide : 104890413 ≤ 104923181) block0 block1

theorem join_0_1 : (twinPrimeSegment 104923181 104988717).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 104923181 ≤ 104955949)
    (by decide : 104955949 ≤ 104988717) block2 block3

theorem join_1_0 : (twinPrimeSegment 104857645 104988717).card = 537 := by
  simpa using combineTwinPrimeSegments (by decide : 104857645 ≤ 104923181)
    (by decide : 104923181 ≤ 104988717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 104857645 104988717).card = 537 := join_1_0

end S050C00
end Sude.GeneratedTwinScan
