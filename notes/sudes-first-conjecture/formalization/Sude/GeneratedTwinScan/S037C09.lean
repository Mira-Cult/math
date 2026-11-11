import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78774317 78807085 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 78774317 78807085).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78774317 78807085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78807085 78839853 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 78807085 78839853).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78807085 78839853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78839853 78872621 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 78839853 78872621).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78839853 78872621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78872621 78905389 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 78872621 78905389).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78872621 78905389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 78774317 78839853).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 78774317 ≤ 78807085)
    (by decide : 78807085 ≤ 78839853) block0 block1

theorem join_0_1 : (twinPrimeSegment 78839853 78905389).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 78839853 ≤ 78872621)
    (by decide : 78872621 ≤ 78905389) block2 block3

theorem join_1_0 : (twinPrimeSegment 78774317 78905389).card = 515 := by
  simpa using combineTwinPrimeSegments (by decide : 78774317 ≤ 78839853)
    (by decide : 78839853 ≤ 78905389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 78774317 78905389).card = 515 := join_1_0

end S037C09
end Sude.GeneratedTwinScan
