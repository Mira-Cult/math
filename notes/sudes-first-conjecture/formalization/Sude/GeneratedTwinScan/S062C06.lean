import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130809901 130842669 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 130809901 130842669).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130809901 130842669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130842669 130875437 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 130842669 130875437).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130842669 130875437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130875437 130908205 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 130875437 130908205).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130875437 130908205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130908205 130940973 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 130908205 130940973).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130908205 130940973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 130809901 130875437).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 130809901 ≤ 130842669)
    (by decide : 130842669 ≤ 130875437) block0 block1

theorem join_0_1 : (twinPrimeSegment 130875437 130940973).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 130875437 ≤ 130908205)
    (by decide : 130908205 ≤ 130940973) block2 block3

theorem join_1_0 : (twinPrimeSegment 130809901 130940973).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 130809901 ≤ 130875437)
    (by decide : 130875437 ≤ 130940973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 130809901 130940973).card = 475 := join_1_0

end S062C06
end Sude.GeneratedTwinScan
