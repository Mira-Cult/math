import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89129005 89161773 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 89129005 89161773).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89129005 89161773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89161773 89194541 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 89161773 89194541).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89161773 89194541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89194541 89227309 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 89194541 89227309).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89194541 89227309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89227309 89260077 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 89227309 89260077).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89227309 89260077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 89129005 89194541).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 89129005 ≤ 89161773)
    (by decide : 89161773 ≤ 89194541) block0 block1

theorem join_0_1 : (twinPrimeSegment 89194541 89260077).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 89194541 ≤ 89227309)
    (by decide : 89227309 ≤ 89260077) block2 block3

theorem join_1_0 : (twinPrimeSegment 89129005 89260077).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 89129005 ≤ 89194541)
    (by decide : 89194541 ≤ 89260077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 89129005 89260077).card = 505 := join_1_0

end S042C08
end Sude.GeneratedTwinScan
