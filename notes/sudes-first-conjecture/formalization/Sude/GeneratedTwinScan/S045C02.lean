import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94634029 94666797 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 94634029 94666797).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94634029 94666797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94666797 94699565 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 94666797 94699565).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94666797 94699565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94699565 94732333 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 94699565 94732333).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94699565 94732333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94732333 94765101 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 94732333 94765101).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94732333 94765101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 94634029 94699565).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 94634029 ≤ 94666797)
    (by decide : 94666797 ≤ 94699565) block0 block1

theorem join_0_1 : (twinPrimeSegment 94699565 94765101).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 94699565 ≤ 94732333)
    (by decide : 94732333 ≤ 94765101) block2 block3

theorem join_1_0 : (twinPrimeSegment 94634029 94765101).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 94634029 ≤ 94699565)
    (by decide : 94699565 ≤ 94765101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 94634029 94765101).card = 521 := join_1_0

end S045C02
end Sude.GeneratedTwinScan
