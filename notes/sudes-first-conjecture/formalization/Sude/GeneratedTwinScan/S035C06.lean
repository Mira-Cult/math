import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74186797 74219565 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 74186797 74219565).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74186797 74219565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74219565 74252333 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 74219565 74252333).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74219565 74252333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74252333 74285101 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 74252333 74285101).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74252333 74285101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74285101 74317869 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 74285101 74317869).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74285101 74317869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 74186797 74252333).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 74186797 ≤ 74219565)
    (by decide : 74219565 ≤ 74252333) block0 block1

theorem join_0_1 : (twinPrimeSegment 74252333 74317869).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 74252333 ≤ 74285101)
    (by decide : 74285101 ≤ 74317869) block2 block3

theorem join_1_0 : (twinPrimeSegment 74186797 74317869).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 74186797 ≤ 74252333)
    (by decide : 74252333 ≤ 74317869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 74186797 74317869).card = 504 := join_1_0

end S035C06
end Sude.GeneratedTwinScan
