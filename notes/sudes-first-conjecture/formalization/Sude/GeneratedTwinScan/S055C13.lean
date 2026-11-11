import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117047341 117080109 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 117047341 117080109).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117047341 117080109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117080109 117112877 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 117080109 117112877).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117080109 117112877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117112877 117145645 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 117112877 117145645).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117112877 117145645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117145645 117178413 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 117145645 117178413).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117145645 117178413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 117047341 117112877).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 117047341 ≤ 117080109)
    (by decide : 117080109 ≤ 117112877) block0 block1

theorem join_0_1 : (twinPrimeSegment 117112877 117178413).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 117112877 ≤ 117145645)
    (by decide : 117145645 ≤ 117178413) block2 block3

theorem join_1_0 : (twinPrimeSegment 117047341 117178413).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 117047341 ≤ 117112877)
    (by decide : 117112877 ≤ 117178413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 117047341 117178413).card = 507 := join_1_0

end S055C13
end Sude.GeneratedTwinScan
