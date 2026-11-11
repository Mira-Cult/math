import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108527661 108560429 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 108527661 108560429).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108527661 108560429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108560429 108593197 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 108560429 108593197).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108560429 108593197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108593197 108625965 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 108593197 108625965).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108593197 108625965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108625965 108658733 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 108625965 108658733).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108625965 108658733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 108527661 108593197).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 108527661 ≤ 108560429)
    (by decide : 108560429 ≤ 108593197) block0 block1

theorem join_0_1 : (twinPrimeSegment 108593197 108658733).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 108593197 ≤ 108625965)
    (by decide : 108625965 ≤ 108658733) block2 block3

theorem join_1_0 : (twinPrimeSegment 108527661 108658733).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 108527661 ≤ 108593197)
    (by decide : 108593197 ≤ 108658733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 108527661 108658733).card = 521 := join_1_0

end S051C12
end Sude.GeneratedTwinScan
