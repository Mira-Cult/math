import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151519277 151552045 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 151519277 151552045).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151519277 151552045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151552045 151584813 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 151552045 151584813).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151552045 151584813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151584813 151617581 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 151584813 151617581).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151584813 151617581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151617581 151650349 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 151617581 151650349).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151617581 151650349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 151519277 151584813).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 151519277 ≤ 151552045)
    (by decide : 151552045 ≤ 151584813) block0 block1

theorem join_0_1 : (twinPrimeSegment 151584813 151650349).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 151584813 ≤ 151617581)
    (by decide : 151617581 ≤ 151650349) block2 block3

theorem join_1_0 : (twinPrimeSegment 151519277 151650349).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 151519277 ≤ 151584813)
    (by decide : 151584813 ≤ 151650349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 151519277 151650349).card = 488 := join_1_0

end S072C04
end Sude.GeneratedTwinScan
