import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61210669 61243437 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 61210669 61243437).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61210669 61243437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61243437 61276205 = 152 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 61243437 61276205).card = 152 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61243437 61276205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61276205 61308973 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 61276205 61308973).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61276205 61308973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61308973 61341741 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 61308973 61341741).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61308973 61341741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 61210669 61276205).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 61210669 ≤ 61243437)
    (by decide : 61243437 ≤ 61276205) block0 block1

theorem join_0_1 : (twinPrimeSegment 61276205 61341741).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 61276205 ≤ 61308973)
    (by decide : 61308973 ≤ 61341741) block2 block3

theorem join_1_0 : (twinPrimeSegment 61210669 61341741).card = 531 := by
  simpa using combineTwinPrimeSegments (by decide : 61210669 ≤ 61276205)
    (by decide : 61276205 ≤ 61341741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 61210669 61341741).card = 531 := join_1_0

end S029C03
end Sude.GeneratedTwinScan
