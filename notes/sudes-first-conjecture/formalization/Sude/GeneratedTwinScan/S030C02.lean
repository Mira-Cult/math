import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63176749 63209517 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 63176749 63209517).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63176749 63209517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63209517 63242285 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 63209517 63242285).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63209517 63242285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63242285 63275053 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 63242285 63275053).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63242285 63275053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63275053 63307821 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 63275053 63307821).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63275053 63307821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 63176749 63242285).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 63176749 ≤ 63209517)
    (by decide : 63209517 ≤ 63242285) block0 block1

theorem join_0_1 : (twinPrimeSegment 63242285 63307821).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 63242285 ≤ 63275053)
    (by decide : 63275053 ≤ 63307821) block2 block3

theorem join_1_0 : (twinPrimeSegment 63176749 63307821).card = 547 := by
  simpa using combineTwinPrimeSegments (by decide : 63176749 ≤ 63242285)
    (by decide : 63242285 ≤ 63307821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 63176749 63307821).card = 547 := join_1_0

end S030C02
end Sude.GeneratedTwinScan
