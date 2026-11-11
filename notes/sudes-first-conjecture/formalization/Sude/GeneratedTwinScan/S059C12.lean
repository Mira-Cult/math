import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125304877 125337645 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 125304877 125337645).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125304877 125337645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125337645 125370413 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 125337645 125370413).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125337645 125370413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125370413 125403181 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 125370413 125403181).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125370413 125403181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125403181 125435949 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 125403181 125435949).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125403181 125435949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 125304877 125370413).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 125304877 ≤ 125337645)
    (by decide : 125337645 ≤ 125370413) block0 block1

theorem join_0_1 : (twinPrimeSegment 125370413 125435949).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 125370413 ≤ 125403181)
    (by decide : 125403181 ≤ 125435949) block2 block3

theorem join_1_0 : (twinPrimeSegment 125304877 125435949).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 125304877 ≤ 125370413)
    (by decide : 125370413 ≤ 125435949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 125304877 125435949).card = 497 := join_1_0

end S059C12
end Sude.GeneratedTwinScan
