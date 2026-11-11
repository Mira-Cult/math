import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80085037 80117805 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 80085037 80117805).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80085037 80117805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80117805 80150573 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 80117805 80150573).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80117805 80150573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80150573 80183341 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 80150573 80183341).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80150573 80183341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80183341 80216109 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 80183341 80216109).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80183341 80216109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 80085037 80150573).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 80085037 ≤ 80117805)
    (by decide : 80117805 ≤ 80150573) block0 block1

theorem join_0_1 : (twinPrimeSegment 80150573 80216109).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 80150573 ≤ 80183341)
    (by decide : 80183341 ≤ 80216109) block2 block3

theorem join_1_0 : (twinPrimeSegment 80085037 80216109).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 80085037 ≤ 80150573)
    (by decide : 80150573 ≤ 80216109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 80085037 80216109).card = 520 := join_1_0

end S038C03
end Sude.GeneratedTwinScan
