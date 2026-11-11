import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125435949 125468717 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 125435949 125468717).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125435949 125468717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125468717 125501485 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 125468717 125501485).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125468717 125501485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125501485 125534253 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 125501485 125534253).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125501485 125534253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125534253 125567021 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 125534253 125567021).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125534253 125567021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 125435949 125501485).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 125435949 ≤ 125468717)
    (by decide : 125468717 ≤ 125501485) block0 block1

theorem join_0_1 : (twinPrimeSegment 125501485 125567021).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 125501485 ≤ 125534253)
    (by decide : 125534253 ≤ 125567021) block2 block3

theorem join_1_0 : (twinPrimeSegment 125435949 125567021).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 125435949 ≤ 125501485)
    (by decide : 125501485 ≤ 125567021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 125435949 125567021).card = 492 := join_1_0

end S059C13
end Sude.GeneratedTwinScan
