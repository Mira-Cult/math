import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79691821 79724589 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 79691821 79724589).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79691821 79724589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79724589 79757357 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 79724589 79757357).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79724589 79757357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79757357 79790125 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 79757357 79790125).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79757357 79790125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79790125 79822893 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 79790125 79822893).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79790125 79822893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 79691821 79757357).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 79691821 ≤ 79724589)
    (by decide : 79724589 ≤ 79757357) block0 block1

theorem join_0_1 : (twinPrimeSegment 79757357 79822893).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 79757357 ≤ 79790125)
    (by decide : 79790125 ≤ 79822893) block2 block3

theorem join_1_0 : (twinPrimeSegment 79691821 79822893).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 79691821 ≤ 79757357)
    (by decide : 79757357 ≤ 79822893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 79691821 79822893).card = 504 := join_1_0

end S038C00
end Sude.GeneratedTwinScan
