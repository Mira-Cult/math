import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132251693 132284461 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 132251693 132284461).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132251693 132284461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132284461 132317229 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 132284461 132317229).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132284461 132317229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132317229 132349997 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 132317229 132349997).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132317229 132349997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132349997 132382765 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 132349997 132382765).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132349997 132382765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 132251693 132317229).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 132251693 ≤ 132284461)
    (by decide : 132284461 ≤ 132317229) block0 block1

theorem join_0_1 : (twinPrimeSegment 132317229 132382765).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 132317229 ≤ 132349997)
    (by decide : 132349997 ≤ 132382765) block2 block3

theorem join_1_0 : (twinPrimeSegment 132251693 132382765).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 132251693 ≤ 132317229)
    (by decide : 132317229 ≤ 132382765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 132251693 132382765).card = 487 := join_1_0

end S063C01
end Sude.GeneratedTwinScan
