import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97255469 97288237 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 97255469 97288237).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97255469 97288237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97288237 97321005 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 97288237 97321005).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97288237 97321005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97321005 97353773 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 97321005 97353773).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97321005 97353773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97353773 97386541 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 97353773 97386541).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97353773 97386541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 97255469 97321005).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 97255469 ≤ 97288237)
    (by decide : 97288237 ≤ 97321005) block0 block1

theorem join_0_1 : (twinPrimeSegment 97321005 97386541).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 97321005 ≤ 97353773)
    (by decide : 97353773 ≤ 97386541) block2 block3

theorem join_1_0 : (twinPrimeSegment 97255469 97386541).card = 527 := by
  simpa using combineTwinPrimeSegments (by decide : 97255469 ≤ 97321005)
    (by decide : 97321005 ≤ 97386541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 97255469 97386541).card = 527 := join_1_0

end S046C06
end Sude.GeneratedTwinScan
