import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115343405 115376173 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 115343405 115376173).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115343405 115376173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115376173 115408941 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 115376173 115408941).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115376173 115408941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115408941 115441709 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 115408941 115441709).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115408941 115441709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115441709 115474477 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 115441709 115474477).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115441709 115474477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 115343405 115408941).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 115343405 ≤ 115376173)
    (by decide : 115376173 ≤ 115408941) block0 block1

theorem join_0_1 : (twinPrimeSegment 115408941 115474477).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 115408941 ≤ 115441709)
    (by decide : 115441709 ≤ 115474477) block2 block3

theorem join_1_0 : (twinPrimeSegment 115343405 115474477).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 115343405 ≤ 115408941)
    (by decide : 115408941 ≤ 115474477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 115343405 115474477).card = 499 := join_1_0

end S055C00
end Sude.GeneratedTwinScan
