import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75235373 75268141 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 75235373 75268141).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75235373 75268141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75268141 75300909 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 75268141 75300909).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75268141 75300909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75300909 75333677 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 75300909 75333677).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75300909 75333677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75333677 75366445 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 75333677 75366445).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75333677 75366445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 75235373 75300909).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 75235373 ≤ 75268141)
    (by decide : 75268141 ≤ 75300909) block0 block1

theorem join_0_1 : (twinPrimeSegment 75300909 75366445).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 75300909 ≤ 75333677)
    (by decide : 75333677 ≤ 75366445) block2 block3

theorem join_1_0 : (twinPrimeSegment 75235373 75366445).card = 536 := by
  simpa using combineTwinPrimeSegments (by decide : 75235373 ≤ 75300909)
    (by decide : 75300909 ≤ 75366445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 75235373 75366445).card = 536 := join_1_0

end S035C14
end Sude.GeneratedTwinScan
