import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128843821 128876589 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 128843821 128876589).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128843821 128876589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128876589 128909357 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 128876589 128909357).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128876589 128909357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128909357 128942125 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 128909357 128942125).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128909357 128942125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128942125 128974893 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 128942125 128974893).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128942125 128974893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 128843821 128909357).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 128843821 ≤ 128876589)
    (by decide : 128876589 ≤ 128909357) block0 block1

theorem join_0_1 : (twinPrimeSegment 128909357 128974893).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 128909357 ≤ 128942125)
    (by decide : 128942125 ≤ 128974893) block2 block3

theorem join_1_0 : (twinPrimeSegment 128843821 128974893).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 128843821 ≤ 128909357)
    (by decide : 128909357 ≤ 128974893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 128843821 128974893).card = 533 := join_1_0

end S061C07
end Sude.GeneratedTwinScan
