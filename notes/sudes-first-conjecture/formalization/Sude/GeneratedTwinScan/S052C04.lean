import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109576237 109609005 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 109576237 109609005).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109576237 109609005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109609005 109641773 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 109609005 109641773).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109609005 109641773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109641773 109674541 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 109641773 109674541).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109641773 109674541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109674541 109707309 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 109674541 109707309).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109674541 109707309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 109576237 109641773).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 109576237 ≤ 109609005)
    (by decide : 109609005 ≤ 109641773) block0 block1

theorem join_0_1 : (twinPrimeSegment 109641773 109707309).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 109641773 ≤ 109674541)
    (by decide : 109674541 ≤ 109707309) block2 block3

theorem join_1_0 : (twinPrimeSegment 109576237 109707309).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 109576237 ≤ 109641773)
    (by decide : 109641773 ≤ 109707309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 109576237 109707309).card = 511 := join_1_0

end S052C04
end Sude.GeneratedTwinScan
