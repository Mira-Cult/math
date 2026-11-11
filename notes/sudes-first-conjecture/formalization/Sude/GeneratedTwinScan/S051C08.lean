import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108003373 108036141 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 108003373 108036141).card = 107 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108003373 108036141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108036141 108068909 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 108036141 108068909).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108036141 108068909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108068909 108101677 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 108068909 108101677).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108068909 108101677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108101677 108134445 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 108101677 108134445).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108101677 108134445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 108003373 108068909).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 108003373 ≤ 108036141)
    (by decide : 108036141 ≤ 108068909) block0 block1

theorem join_0_1 : (twinPrimeSegment 108068909 108134445).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 108068909 ≤ 108101677)
    (by decide : 108101677 ≤ 108134445) block2 block3

theorem join_1_0 : (twinPrimeSegment 108003373 108134445).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 108003373 ≤ 108068909)
    (by decide : 108068909 ≤ 108134445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 108003373 108134445).card = 490 := join_1_0

end S051C08
end Sude.GeneratedTwinScan
