import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148897837 148930605 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 148897837 148930605).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148897837 148930605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148930605 148963373 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 148930605 148963373).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148930605 148963373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148963373 148996141 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 148963373 148996141).card = 104 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148963373 148996141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148996141 149028909 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 148996141 149028909).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148996141 149028909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 148897837 148963373).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 148897837 ≤ 148930605)
    (by decide : 148930605 ≤ 148963373) block0 block1

theorem join_0_1 : (twinPrimeSegment 148963373 149028909).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 148963373 ≤ 148996141)
    (by decide : 148996141 ≤ 149028909) block2 block3

theorem join_1_0 : (twinPrimeSegment 148897837 149028909).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 148897837 ≤ 148963373)
    (by decide : 148963373 ≤ 149028909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 148897837 149028909).card = 511 := join_1_0

end S071C00
end Sude.GeneratedTwinScan
