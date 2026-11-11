import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103940141 103972909 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 103940141 103972909).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103940141 103972909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103972909 104005677 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 103972909 104005677).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103972909 104005677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104005677 104038445 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 104005677 104038445).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104005677 104038445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104038445 104071213 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 104038445 104071213).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104038445 104071213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 103940141 104005677).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 103940141 ≤ 103972909)
    (by decide : 103972909 ≤ 104005677) block0 block1

theorem join_0_1 : (twinPrimeSegment 104005677 104071213).card = 290 := by
  simpa using combineTwinPrimeSegments (by decide : 104005677 ≤ 104038445)
    (by decide : 104038445 ≤ 104071213) block2 block3

theorem join_1_0 : (twinPrimeSegment 103940141 104071213).card = 556 := by
  simpa using combineTwinPrimeSegments (by decide : 103940141 ≤ 104005677)
    (by decide : 104005677 ≤ 104071213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 103940141 104071213).card = 556 := join_1_0

end S049C09
end Sude.GeneratedTwinScan
