import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98828333 98861101 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 98828333 98861101).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98828333 98861101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98861101 98893869 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 98861101 98893869).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98861101 98893869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98893869 98926637 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 98893869 98926637).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98893869 98926637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98926637 98959405 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 98926637 98959405).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98926637 98959405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 98828333 98893869).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 98828333 ≤ 98861101)
    (by decide : 98861101 ≤ 98893869) block0 block1

theorem join_0_1 : (twinPrimeSegment 98893869 98959405).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 98893869 ≤ 98926637)
    (by decide : 98926637 ≤ 98959405) block2 block3

theorem join_1_0 : (twinPrimeSegment 98828333 98959405).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 98828333 ≤ 98893869)
    (by decide : 98893869 ≤ 98959405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 98828333 98959405).card = 508 := join_1_0

end S047C02
end Sude.GeneratedTwinScan
