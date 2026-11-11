import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112197677 112230445 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 112197677 112230445).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112197677 112230445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112230445 112263213 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 112230445 112263213).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112230445 112263213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112263213 112295981 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 112263213 112295981).card = 102 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112263213 112295981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112295981 112328749 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 112295981 112328749).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112295981 112328749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 112197677 112263213).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 112197677 ≤ 112230445)
    (by decide : 112230445 ≤ 112263213) block0 block1

theorem join_0_1 : (twinPrimeSegment 112263213 112328749).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 112263213 ≤ 112295981)
    (by decide : 112295981 ≤ 112328749) block2 block3

theorem join_1_0 : (twinPrimeSegment 112197677 112328749).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 112197677 ≤ 112263213)
    (by decide : 112263213 ≤ 112328749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 112197677 112328749).card = 450 := join_1_0

end S053C08
end Sude.GeneratedTwinScan
