import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143130669 143163437 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 143130669 143163437).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143130669 143163437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143163437 143196205 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 143163437 143196205).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143163437 143196205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143196205 143228973 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 143196205 143228973).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143196205 143228973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143228973 143261741 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 143228973 143261741).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143228973 143261741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 143130669 143196205).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 143130669 ≤ 143163437)
    (by decide : 143163437 ≤ 143196205) block0 block1

theorem join_0_1 : (twinPrimeSegment 143196205 143261741).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 143196205 ≤ 143228973)
    (by decide : 143228973 ≤ 143261741) block2 block3

theorem join_1_0 : (twinPrimeSegment 143130669 143261741).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 143130669 ≤ 143196205)
    (by decide : 143196205 ≤ 143261741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 143130669 143261741).card = 472 := join_1_0

end S068C04
end Sude.GeneratedTwinScan
