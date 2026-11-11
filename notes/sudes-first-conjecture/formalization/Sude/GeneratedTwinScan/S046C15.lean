import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98435117 98467885 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 98435117 98467885).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98435117 98467885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98467885 98500653 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 98467885 98500653).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98467885 98500653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98500653 98533421 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 98500653 98533421).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98500653 98533421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98533421 98566189 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 98533421 98566189).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98533421 98566189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 98435117 98500653).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 98435117 ≤ 98467885)
    (by decide : 98467885 ≤ 98500653) block0 block1

theorem join_0_1 : (twinPrimeSegment 98500653 98566189).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 98500653 ≤ 98533421)
    (by decide : 98533421 ≤ 98566189) block2 block3

theorem join_1_0 : (twinPrimeSegment 98435117 98566189).card = 539 := by
  simpa using combineTwinPrimeSegments (by decide : 98435117 ≤ 98500653)
    (by decide : 98500653 ≤ 98566189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 98435117 98566189).card = 539 := join_1_0

end S046C15
end Sude.GeneratedTwinScan
