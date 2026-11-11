import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87687213 87719981 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 87687213 87719981).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87687213 87719981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87719981 87752749 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 87719981 87752749).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87719981 87752749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87752749 87785517 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 87752749 87785517).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87752749 87785517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87785517 87818285 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 87785517 87818285).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87785517 87818285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 87687213 87752749).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 87687213 ≤ 87719981)
    (by decide : 87719981 ≤ 87752749) block0 block1

theorem join_0_1 : (twinPrimeSegment 87752749 87818285).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 87752749 ≤ 87785517)
    (by decide : 87785517 ≤ 87818285) block2 block3

theorem join_1_0 : (twinPrimeSegment 87687213 87818285).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 87687213 ≤ 87752749)
    (by decide : 87752749 ≤ 87818285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 87687213 87818285).card = 500 := join_1_0

end S041C13
end Sude.GeneratedTwinScan
