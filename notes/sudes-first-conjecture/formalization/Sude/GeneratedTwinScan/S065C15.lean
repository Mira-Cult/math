import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138281005 138313773 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 138281005 138313773).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138281005 138313773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138313773 138346541 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 138313773 138346541).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138313773 138346541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138346541 138379309 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 138346541 138379309).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138346541 138379309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138379309 138412077 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 138379309 138412077).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138379309 138412077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 138281005 138346541).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 138281005 ≤ 138313773)
    (by decide : 138313773 ≤ 138346541) block0 block1

theorem join_0_1 : (twinPrimeSegment 138346541 138412077).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 138346541 ≤ 138379309)
    (by decide : 138379309 ≤ 138412077) block2 block3

theorem join_1_0 : (twinPrimeSegment 138281005 138412077).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 138281005 ≤ 138346541)
    (by decide : 138346541 ≤ 138412077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 138281005 138412077).card = 495 := join_1_0

end S065C15
end Sude.GeneratedTwinScan
