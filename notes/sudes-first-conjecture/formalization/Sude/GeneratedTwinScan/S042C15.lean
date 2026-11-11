import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90046509 90079277 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 90046509 90079277).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90046509 90079277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90079277 90112045 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 90079277 90112045).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90079277 90112045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90112045 90144813 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 90112045 90144813).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90112045 90144813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90144813 90177581 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 90144813 90177581).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90144813 90177581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 90046509 90112045).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 90046509 ≤ 90079277)
    (by decide : 90079277 ≤ 90112045) block0 block1

theorem join_0_1 : (twinPrimeSegment 90112045 90177581).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 90112045 ≤ 90144813)
    (by decide : 90144813 ≤ 90177581) block2 block3

theorem join_1_0 : (twinPrimeSegment 90046509 90177581).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 90046509 ≤ 90112045)
    (by decide : 90112045 ≤ 90177581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 90046509 90177581).card = 510 := join_1_0

end S042C15
end Sude.GeneratedTwinScan
