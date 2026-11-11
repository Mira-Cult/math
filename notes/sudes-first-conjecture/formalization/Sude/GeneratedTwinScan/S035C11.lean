import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74842157 74874925 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 74842157 74874925).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74842157 74874925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74874925 74907693 = 150 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 74874925 74907693).card = 150 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74874925 74907693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74907693 74940461 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 74907693 74940461).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74907693 74940461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74940461 74973229 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 74940461 74973229).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74940461 74973229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 74842157 74907693).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 74842157 ≤ 74874925)
    (by decide : 74874925 ≤ 74907693) block0 block1

theorem join_0_1 : (twinPrimeSegment 74907693 74973229).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 74907693 ≤ 74940461)
    (by decide : 74940461 ≤ 74973229) block2 block3

theorem join_1_0 : (twinPrimeSegment 74842157 74973229).card = 552 := by
  simpa using combineTwinPrimeSegments (by decide : 74842157 ≤ 74907693)
    (by decide : 74907693 ≤ 74973229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 74842157 74973229).card = 552 := join_1_0

end S035C11
end Sude.GeneratedTwinScan
