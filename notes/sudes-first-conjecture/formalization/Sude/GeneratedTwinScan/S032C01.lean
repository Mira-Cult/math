import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67239981 67272749 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 67239981 67272749).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67239981 67272749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67272749 67305517 = 151 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 67272749 67305517).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67272749 67305517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67305517 67338285 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 67305517 67338285).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67305517 67338285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67338285 67371053 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 67338285 67371053).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67338285 67371053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 67239981 67305517).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 67239981 ≤ 67272749)
    (by decide : 67272749 ≤ 67305517) block0 block1

theorem join_0_1 : (twinPrimeSegment 67305517 67371053).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 67305517 ≤ 67338285)
    (by decide : 67338285 ≤ 67371053) block2 block3

theorem join_1_0 : (twinPrimeSegment 67239981 67371053).card = 563 := by
  simpa using combineTwinPrimeSegments (by decide : 67239981 ≤ 67305517)
    (by decide : 67305517 ≤ 67371053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 67239981 67371053).card = 563 := join_1_0

end S032C01
end Sude.GeneratedTwinScan
