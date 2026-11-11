import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119406637 119439405 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 119406637 119439405).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119406637 119439405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119439405 119472173 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 119439405 119472173).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119439405 119472173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119472173 119504941 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 119472173 119504941).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119472173 119504941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119504941 119537709 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 119504941 119537709).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119504941 119537709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 119406637 119472173).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 119406637 ≤ 119439405)
    (by decide : 119439405 ≤ 119472173) block0 block1

theorem join_0_1 : (twinPrimeSegment 119472173 119537709).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 119472173 ≤ 119504941)
    (by decide : 119504941 ≤ 119537709) block2 block3

theorem join_1_0 : (twinPrimeSegment 119406637 119537709).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 119406637 ≤ 119472173)
    (by decide : 119472173 ≤ 119537709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 119406637 119537709).card = 508 := join_1_0

end S056C15
end Sude.GeneratedTwinScan
