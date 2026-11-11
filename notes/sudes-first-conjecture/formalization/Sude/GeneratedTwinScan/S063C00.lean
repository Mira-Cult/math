import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132120621 132153389 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 132120621 132153389).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132120621 132153389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132153389 132186157 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 132153389 132186157).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132153389 132186157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132186157 132218925 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 132186157 132218925).card = 106 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132186157 132218925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132218925 132251693 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 132218925 132251693).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132218925 132251693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 132120621 132186157).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 132120621 ≤ 132153389)
    (by decide : 132153389 ≤ 132186157) block0 block1

theorem join_0_1 : (twinPrimeSegment 132186157 132251693).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 132186157 ≤ 132218925)
    (by decide : 132218925 ≤ 132251693) block2 block3

theorem join_1_0 : (twinPrimeSegment 132120621 132251693).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 132120621 ≤ 132186157)
    (by decide : 132186157 ≤ 132251693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 132120621 132251693).card = 493 := join_1_0

end S063C00
end Sude.GeneratedTwinScan
