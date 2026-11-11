import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95813677 95846445 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 95813677 95846445).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95813677 95846445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95846445 95879213 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 95846445 95879213).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95846445 95879213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95879213 95911981 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 95879213 95911981).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95879213 95911981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95911981 95944749 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 95911981 95944749).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95911981 95944749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 95813677 95879213).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 95813677 ≤ 95846445)
    (by decide : 95846445 ≤ 95879213) block0 block1

theorem join_0_1 : (twinPrimeSegment 95879213 95944749).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 95879213 ≤ 95911981)
    (by decide : 95911981 ≤ 95944749) block2 block3

theorem join_1_0 : (twinPrimeSegment 95813677 95944749).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 95813677 ≤ 95879213)
    (by decide : 95879213 ≤ 95944749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 95813677 95944749).card = 500 := join_1_0

end S045C11
end Sude.GeneratedTwinScan
