import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128581677 128614445 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 128581677 128614445).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128581677 128614445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128614445 128647213 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 128614445 128647213).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128614445 128647213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128647213 128679981 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 128647213 128679981).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128647213 128679981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128679981 128712749 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 128679981 128712749).card = 107 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128679981 128712749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 128581677 128647213).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 128581677 ≤ 128614445)
    (by decide : 128614445 ≤ 128647213) block0 block1

theorem join_0_1 : (twinPrimeSegment 128647213 128712749).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 128647213 ≤ 128679981)
    (by decide : 128679981 ≤ 128712749) block2 block3

theorem join_1_0 : (twinPrimeSegment 128581677 128712749).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 128581677 ≤ 128647213)
    (by decide : 128647213 ≤ 128712749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 128581677 128712749).card = 485 := join_1_0

end S061C05
end Sude.GeneratedTwinScan
