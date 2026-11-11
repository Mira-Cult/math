import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90177581 90210349 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 90177581 90210349).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90177581 90210349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90210349 90243117 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 90210349 90243117).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90210349 90243117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90243117 90275885 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 90243117 90275885).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90243117 90275885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90275885 90308653 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 90275885 90308653).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90275885 90308653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 90177581 90243117).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 90177581 ≤ 90210349)
    (by decide : 90210349 ≤ 90243117) block0 block1

theorem join_0_1 : (twinPrimeSegment 90243117 90308653).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 90243117 ≤ 90275885)
    (by decide : 90275885 ≤ 90308653) block2 block3

theorem join_1_0 : (twinPrimeSegment 90177581 90308653).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 90177581 ≤ 90243117)
    (by decide : 90243117 ≤ 90308653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 90177581 90308653).card = 514 := join_1_0

end S043C00
end Sude.GeneratedTwinScan
