import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63045677 63078445 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 63045677 63078445).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63045677 63078445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63078445 63111213 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 63078445 63111213).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63078445 63111213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63111213 63143981 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 63111213 63143981).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63111213 63143981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63143981 63176749 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 63143981 63176749).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63143981 63176749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 63045677 63111213).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 63045677 ≤ 63078445)
    (by decide : 63078445 ≤ 63111213) block0 block1

theorem join_0_1 : (twinPrimeSegment 63111213 63176749).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 63111213 ≤ 63143981)
    (by decide : 63143981 ≤ 63176749) block2 block3

theorem join_1_0 : (twinPrimeSegment 63045677 63176749).card = 545 := by
  simpa using combineTwinPrimeSegments (by decide : 63045677 ≤ 63111213)
    (by decide : 63111213 ≤ 63176749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 63045677 63176749).card = 545 := join_1_0

end S030C01
end Sude.GeneratedTwinScan
