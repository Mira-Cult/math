import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88735789 88768557 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 88735789 88768557).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88735789 88768557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88768557 88801325 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 88768557 88801325).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88768557 88801325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88801325 88834093 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 88801325 88834093).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88801325 88834093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88834093 88866861 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 88834093 88866861).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88834093 88866861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 88735789 88801325).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 88735789 ≤ 88768557)
    (by decide : 88768557 ≤ 88801325) block0 block1

theorem join_0_1 : (twinPrimeSegment 88801325 88866861).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 88801325 ≤ 88834093)
    (by decide : 88834093 ≤ 88866861) block2 block3

theorem join_1_0 : (twinPrimeSegment 88735789 88866861).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 88735789 ≤ 88801325)
    (by decide : 88801325 ≤ 88866861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 88735789 88866861).card = 524 := join_1_0

end S042C05
end Sude.GeneratedTwinScan
