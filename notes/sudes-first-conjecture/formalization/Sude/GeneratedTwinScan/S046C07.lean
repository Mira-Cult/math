import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97386541 97419309 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 97386541 97419309).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97386541 97419309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97419309 97452077 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 97419309 97452077).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97419309 97452077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97452077 97484845 = 152 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 97452077 97484845).card = 152 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97452077 97484845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97484845 97517613 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 97484845 97517613).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97484845 97517613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 97386541 97452077).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 97386541 ≤ 97419309)
    (by decide : 97419309 ≤ 97452077) block0 block1

theorem join_0_1 : (twinPrimeSegment 97452077 97517613).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 97452077 ≤ 97484845)
    (by decide : 97484845 ≤ 97517613) block2 block3

theorem join_1_0 : (twinPrimeSegment 97386541 97517613).card = 526 := by
  simpa using combineTwinPrimeSegments (by decide : 97386541 ≤ 97452077)
    (by decide : 97452077 ≤ 97517613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 97386541 97517613).card = 526 := join_1_0

end S046C07
end Sude.GeneratedTwinScan
