import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93978669 94011437 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 93978669 94011437).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93978669 94011437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94011437 94044205 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 94011437 94044205).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94011437 94044205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94044205 94076973 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 94044205 94076973).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94044205 94076973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94076973 94109741 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 94076973 94109741).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94076973 94109741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 93978669 94044205).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 93978669 ≤ 94011437)
    (by decide : 94011437 ≤ 94044205) block0 block1

theorem join_0_1 : (twinPrimeSegment 94044205 94109741).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 94044205 ≤ 94076973)
    (by decide : 94076973 ≤ 94109741) block2 block3

theorem join_1_0 : (twinPrimeSegment 93978669 94109741).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 93978669 ≤ 94044205)
    (by decide : 94044205 ≤ 94109741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 93978669 94109741).card = 511 := join_1_0

end S044C13
end Sude.GeneratedTwinScan
