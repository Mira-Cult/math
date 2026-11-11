import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133824557 133857325 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 133824557 133857325).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133824557 133857325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133857325 133890093 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 133857325 133890093).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133857325 133890093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133890093 133922861 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 133890093 133922861).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133890093 133922861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133922861 133955629 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 133922861 133955629).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133922861 133955629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 133824557 133890093).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 133824557 ≤ 133857325)
    (by decide : 133857325 ≤ 133890093) block0 block1

theorem join_0_1 : (twinPrimeSegment 133890093 133955629).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 133890093 ≤ 133922861)
    (by decide : 133922861 ≤ 133955629) block2 block3

theorem join_1_0 : (twinPrimeSegment 133824557 133955629).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 133824557 ≤ 133890093)
    (by decide : 133890093 ≤ 133955629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 133824557 133955629).card = 496 := join_1_0

end S063C13
end Sude.GeneratedTwinScan
