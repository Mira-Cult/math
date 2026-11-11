import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94109741 94142509 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 94109741 94142509).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94109741 94142509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94142509 94175277 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 94142509 94175277).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94142509 94175277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94175277 94208045 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 94175277 94208045).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94175277 94208045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94208045 94240813 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 94208045 94240813).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94208045 94240813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 94109741 94175277).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 94109741 ≤ 94142509)
    (by decide : 94142509 ≤ 94175277) block0 block1

theorem join_0_1 : (twinPrimeSegment 94175277 94240813).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 94175277 ≤ 94208045)
    (by decide : 94208045 ≤ 94240813) block2 block3

theorem join_1_0 : (twinPrimeSegment 94109741 94240813).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 94109741 ≤ 94175277)
    (by decide : 94175277 ≤ 94240813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 94109741 94240813).card = 507 := join_1_0

end S044C14
end Sude.GeneratedTwinScan
