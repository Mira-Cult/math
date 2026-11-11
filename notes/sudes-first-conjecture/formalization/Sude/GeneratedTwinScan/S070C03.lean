import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147193901 147226669 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 147193901 147226669).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147193901 147226669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147226669 147259437 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 147226669 147259437).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147226669 147259437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147259437 147292205 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 147259437 147292205).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147259437 147292205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147292205 147324973 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 147292205 147324973).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147292205 147324973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 147193901 147259437).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 147193901 ≤ 147226669)
    (by decide : 147226669 ≤ 147259437) block0 block1

theorem join_0_1 : (twinPrimeSegment 147259437 147324973).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 147259437 ≤ 147292205)
    (by decide : 147292205 ≤ 147324973) block2 block3

theorem join_1_0 : (twinPrimeSegment 147193901 147324973).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 147193901 ≤ 147259437)
    (by decide : 147259437 ≤ 147324973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 147193901 147324973).card = 491 := join_1_0

end S070C03
end Sude.GeneratedTwinScan
