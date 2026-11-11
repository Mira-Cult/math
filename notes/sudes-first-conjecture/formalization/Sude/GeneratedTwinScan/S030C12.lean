import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64487469 64520237 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 64487469 64520237).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64487469 64520237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64520237 64553005 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 64520237 64553005).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64520237 64553005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64553005 64585773 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 64553005 64585773).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64553005 64585773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64585773 64618541 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 64585773 64618541).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64585773 64618541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 64487469 64553005).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 64487469 ≤ 64520237)
    (by decide : 64520237 ≤ 64553005) block0 block1

theorem join_0_1 : (twinPrimeSegment 64553005 64618541).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 64553005 ≤ 64585773)
    (by decide : 64585773 ≤ 64618541) block2 block3

theorem join_1_0 : (twinPrimeSegment 64487469 64618541).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 64487469 ≤ 64553005)
    (by decide : 64553005 ≤ 64618541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 64487469 64618541).card = 496 := join_1_0

end S030C12
end Sude.GeneratedTwinScan
