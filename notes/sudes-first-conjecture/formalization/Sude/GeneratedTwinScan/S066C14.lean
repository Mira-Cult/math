import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140247085 140279853 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 140247085 140279853).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140247085 140279853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140279853 140312621 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 140279853 140312621).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140279853 140312621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140312621 140345389 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 140312621 140345389).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140312621 140345389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140345389 140378157 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 140345389 140378157).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140345389 140378157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 140247085 140312621).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 140247085 ≤ 140279853)
    (by decide : 140279853 ≤ 140312621) block0 block1

theorem join_0_1 : (twinPrimeSegment 140312621 140378157).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 140312621 ≤ 140345389)
    (by decide : 140345389 ≤ 140378157) block2 block3

theorem join_1_0 : (twinPrimeSegment 140247085 140378157).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 140247085 ≤ 140312621)
    (by decide : 140312621 ≤ 140378157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 140247085 140378157).card = 483 := join_1_0

end S066C14
end Sude.GeneratedTwinScan
