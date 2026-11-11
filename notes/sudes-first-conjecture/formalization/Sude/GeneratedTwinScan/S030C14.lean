import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64749613 64782381 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 64749613 64782381).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64749613 64782381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64782381 64815149 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 64782381 64815149).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64782381 64815149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64815149 64847917 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 64815149 64847917).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64815149 64847917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64847917 64880685 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 64847917 64880685).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64847917 64880685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 64749613 64815149).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 64749613 ≤ 64782381)
    (by decide : 64782381 ≤ 64815149) block0 block1

theorem join_0_1 : (twinPrimeSegment 64815149 64880685).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 64815149 ≤ 64847917)
    (by decide : 64847917 ≤ 64880685) block2 block3

theorem join_1_0 : (twinPrimeSegment 64749613 64880685).card = 555 := by
  simpa using combineTwinPrimeSegments (by decide : 64749613 ≤ 64815149)
    (by decide : 64815149 ≤ 64880685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 64749613 64880685).card = 555 := join_1_0

end S030C14
end Sude.GeneratedTwinScan
