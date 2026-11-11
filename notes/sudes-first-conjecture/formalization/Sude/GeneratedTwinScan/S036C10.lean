import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76808237 76841005 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 76808237 76841005).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76808237 76841005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76841005 76873773 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 76841005 76873773).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76841005 76873773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76873773 76906541 = 148 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 76873773 76906541).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76873773 76906541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76906541 76939309 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 76906541 76939309).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76906541 76939309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 76808237 76873773).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 76808237 ≤ 76841005)
    (by decide : 76841005 ≤ 76873773) block0 block1

theorem join_0_1 : (twinPrimeSegment 76873773 76939309).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 76873773 ≤ 76906541)
    (by decide : 76906541 ≤ 76939309) block2 block3

theorem join_1_0 : (twinPrimeSegment 76808237 76939309).card = 553 := by
  simpa using combineTwinPrimeSegments (by decide : 76808237 ≤ 76873773)
    (by decide : 76873773 ≤ 76939309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 76808237 76939309).card = 553 := join_1_0

end S036C10
end Sude.GeneratedTwinScan
