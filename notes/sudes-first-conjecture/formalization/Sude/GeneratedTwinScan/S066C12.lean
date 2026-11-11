import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139984941 140017709 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 139984941 140017709).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139984941 140017709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140017709 140050477 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 140017709 140050477).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140017709 140050477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140050477 140083245 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 140050477 140083245).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140050477 140083245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140083245 140116013 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 140083245 140116013).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140083245 140116013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 139984941 140050477).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 139984941 ≤ 140017709)
    (by decide : 140017709 ≤ 140050477) block0 block1

theorem join_0_1 : (twinPrimeSegment 140050477 140116013).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 140050477 ≤ 140083245)
    (by decide : 140083245 ≤ 140116013) block2 block3

theorem join_1_0 : (twinPrimeSegment 139984941 140116013).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 139984941 ≤ 140050477)
    (by decide : 140050477 ≤ 140116013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 139984941 140116013).card = 494 := join_1_0

end S066C12
end Sude.GeneratedTwinScan
