import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127533101 127565869 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 127533101 127565869).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127533101 127565869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127565869 127598637 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 127565869 127598637).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127565869 127598637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127598637 127631405 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 127598637 127631405).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127598637 127631405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127631405 127664173 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 127631405 127664173).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127631405 127664173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 127533101 127598637).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 127533101 ≤ 127565869)
    (by decide : 127565869 ≤ 127598637) block0 block1

theorem join_0_1 : (twinPrimeSegment 127598637 127664173).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 127598637 ≤ 127631405)
    (by decide : 127631405 ≤ 127664173) block2 block3

theorem join_1_0 : (twinPrimeSegment 127533101 127664173).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 127533101 ≤ 127598637)
    (by decide : 127598637 ≤ 127664173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 127533101 127664173).card = 497 := join_1_0

end S060C13
end Sude.GeneratedTwinScan
