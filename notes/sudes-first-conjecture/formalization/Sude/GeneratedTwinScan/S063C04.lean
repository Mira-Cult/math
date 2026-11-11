import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132644909 132677677 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 132644909 132677677).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132644909 132677677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132677677 132710445 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 132677677 132710445).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132677677 132710445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132710445 132743213 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 132710445 132743213).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132710445 132743213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132743213 132775981 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 132743213 132775981).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132743213 132775981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 132644909 132710445).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 132644909 ≤ 132677677)
    (by decide : 132677677 ≤ 132710445) block0 block1

theorem join_0_1 : (twinPrimeSegment 132710445 132775981).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 132710445 ≤ 132743213)
    (by decide : 132743213 ≤ 132775981) block2 block3

theorem join_1_0 : (twinPrimeSegment 132644909 132775981).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 132644909 ≤ 132710445)
    (by decide : 132710445 ≤ 132775981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 132644909 132775981).card = 499 := join_1_0

end S063C04
end Sude.GeneratedTwinScan
