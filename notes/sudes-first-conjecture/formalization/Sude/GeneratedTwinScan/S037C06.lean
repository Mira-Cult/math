import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78381101 78413869 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 78381101 78413869).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78381101 78413869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78413869 78446637 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 78413869 78446637).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78413869 78446637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78446637 78479405 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 78446637 78479405).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78446637 78479405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78479405 78512173 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 78479405 78512173).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78479405 78512173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 78381101 78446637).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 78381101 ≤ 78413869)
    (by decide : 78413869 ≤ 78446637) block0 block1

theorem join_0_1 : (twinPrimeSegment 78446637 78512173).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 78446637 ≤ 78479405)
    (by decide : 78479405 ≤ 78512173) block2 block3

theorem join_1_0 : (twinPrimeSegment 78381101 78512173).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 78381101 ≤ 78446637)
    (by decide : 78446637 ≤ 78512173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 78381101 78512173).card = 500 := join_1_0

end S037C06
end Sude.GeneratedTwinScan
