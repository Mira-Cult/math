import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91619373 91652141 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 91619373 91652141).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91619373 91652141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91652141 91684909 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 91652141 91684909).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91652141 91684909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91684909 91717677 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 91684909 91717677).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91684909 91717677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91717677 91750445 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 91717677 91750445).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91717677 91750445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 91619373 91684909).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 91619373 ≤ 91652141)
    (by decide : 91652141 ≤ 91684909) block0 block1

theorem join_0_1 : (twinPrimeSegment 91684909 91750445).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 91684909 ≤ 91717677)
    (by decide : 91717677 ≤ 91750445) block2 block3

theorem join_1_0 : (twinPrimeSegment 91619373 91750445).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 91619373 ≤ 91684909)
    (by decide : 91684909 ≤ 91750445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 91619373 91750445).card = 534 := join_1_0

end S043C11
end Sude.GeneratedTwinScan
