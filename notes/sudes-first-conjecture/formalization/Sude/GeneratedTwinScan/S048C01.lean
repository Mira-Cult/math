import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100794413 100827181 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 100794413 100827181).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100794413 100827181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100827181 100859949 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 100827181 100859949).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100827181 100859949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100859949 100892717 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 100859949 100892717).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100859949 100892717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100892717 100925485 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 100892717 100925485).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100892717 100925485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 100794413 100859949).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 100794413 ≤ 100827181)
    (by decide : 100827181 ≤ 100859949) block0 block1

theorem join_0_1 : (twinPrimeSegment 100859949 100925485).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 100859949 ≤ 100892717)
    (by decide : 100892717 ≤ 100925485) block2 block3

theorem join_1_0 : (twinPrimeSegment 100794413 100925485).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 100794413 ≤ 100859949)
    (by decide : 100859949 ≤ 100925485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 100794413 100925485).card = 502 := join_1_0

end S048C01
end Sude.GeneratedTwinScan
