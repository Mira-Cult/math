import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117440557 117473325 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 117440557 117473325).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117440557 117473325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117473325 117506093 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 117473325 117506093).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117473325 117506093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117506093 117538861 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 117506093 117538861).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117506093 117538861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117538861 117571629 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 117538861 117571629).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117538861 117571629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 117440557 117506093).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 117440557 ≤ 117473325)
    (by decide : 117473325 ≤ 117506093) block0 block1

theorem join_0_1 : (twinPrimeSegment 117506093 117571629).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 117506093 ≤ 117538861)
    (by decide : 117538861 ≤ 117571629) block2 block3

theorem join_1_0 : (twinPrimeSegment 117440557 117571629).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 117440557 ≤ 117506093)
    (by decide : 117506093 ≤ 117571629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 117440557 117571629).card = 501 := join_1_0

end S056C00
end Sude.GeneratedTwinScan
