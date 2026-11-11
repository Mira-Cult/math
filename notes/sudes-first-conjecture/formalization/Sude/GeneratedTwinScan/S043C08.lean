import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91226157 91258925 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 91226157 91258925).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91226157 91258925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91258925 91291693 = 148 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 91258925 91291693).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91258925 91291693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91291693 91324461 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 91291693 91324461).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91291693 91324461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91324461 91357229 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 91324461 91357229).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91324461 91357229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 91226157 91291693).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 91226157 ≤ 91258925)
    (by decide : 91258925 ≤ 91291693) block0 block1

theorem join_0_1 : (twinPrimeSegment 91291693 91357229).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 91291693 ≤ 91324461)
    (by decide : 91324461 ≤ 91357229) block2 block3

theorem join_1_0 : (twinPrimeSegment 91226157 91357229).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 91226157 ≤ 91291693)
    (by decide : 91291693 ≤ 91357229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 91226157 91357229).card = 524 := join_1_0

end S043C08
end Sude.GeneratedTwinScan
