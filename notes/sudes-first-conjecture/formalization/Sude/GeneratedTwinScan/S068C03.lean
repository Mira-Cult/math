import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142999597 143032365 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 142999597 143032365).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142999597 143032365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143032365 143065133 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 143032365 143065133).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143032365 143065133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143065133 143097901 = 145 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 143065133 143097901).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143065133 143097901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143097901 143130669 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 143097901 143130669).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143097901 143130669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 142999597 143065133).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 142999597 ≤ 143032365)
    (by decide : 143032365 ≤ 143065133) block0 block1

theorem join_0_1 : (twinPrimeSegment 143065133 143130669).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 143065133 ≤ 143097901)
    (by decide : 143097901 ≤ 143130669) block2 block3

theorem join_1_0 : (twinPrimeSegment 142999597 143130669).card = 518 := by
  simpa using combineTwinPrimeSegments (by decide : 142999597 ≤ 143065133)
    (by decide : 143065133 ≤ 143130669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 142999597 143130669).card = 518 := join_1_0

end S068C03
end Sude.GeneratedTwinScan
