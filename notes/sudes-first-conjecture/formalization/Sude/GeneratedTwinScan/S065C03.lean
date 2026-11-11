import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136708141 136740909 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 136708141 136740909).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136708141 136740909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136740909 136773677 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 136740909 136773677).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136740909 136773677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136773677 136806445 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 136773677 136806445).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136773677 136806445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136806445 136839213 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 136806445 136839213).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136806445 136839213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 136708141 136773677).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 136708141 ≤ 136740909)
    (by decide : 136740909 ≤ 136773677) block0 block1

theorem join_0_1 : (twinPrimeSegment 136773677 136839213).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 136773677 ≤ 136806445)
    (by decide : 136806445 ≤ 136839213) block2 block3

theorem join_1_0 : (twinPrimeSegment 136708141 136839213).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 136708141 ≤ 136773677)
    (by decide : 136773677 ≤ 136839213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 136708141 136839213).card = 499 := join_1_0

end S065C03
end Sude.GeneratedTwinScan
