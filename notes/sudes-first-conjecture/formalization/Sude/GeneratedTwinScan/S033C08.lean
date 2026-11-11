import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70254637 70287405 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 70254637 70287405).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70254637 70287405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70287405 70320173 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 70287405 70320173).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70287405 70320173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70320173 70352941 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 70320173 70352941).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70320173 70352941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70352941 70385709 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 70352941 70385709).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70352941 70385709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 70254637 70320173).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 70254637 ≤ 70287405)
    (by decide : 70287405 ≤ 70320173) block0 block1

theorem join_0_1 : (twinPrimeSegment 70320173 70385709).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 70320173 ≤ 70352941)
    (by decide : 70352941 ≤ 70385709) block2 block3

theorem join_1_0 : (twinPrimeSegment 70254637 70385709).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 70254637 ≤ 70320173)
    (by decide : 70320173 ≤ 70385709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 70254637 70385709).card = 534 := join_1_0

end S033C08
end Sude.GeneratedTwinScan
