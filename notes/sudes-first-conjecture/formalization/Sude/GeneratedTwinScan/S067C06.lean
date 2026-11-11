import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141295661 141328429 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 141295661 141328429).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141295661 141328429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141328429 141361197 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 141328429 141361197).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141328429 141361197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141361197 141393965 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 141361197 141393965).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141361197 141393965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141393965 141426733 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 141393965 141426733).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141393965 141426733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 141295661 141361197).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 141295661 ≤ 141328429)
    (by decide : 141328429 ≤ 141361197) block0 block1

theorem join_0_1 : (twinPrimeSegment 141361197 141426733).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 141361197 ≤ 141393965)
    (by decide : 141393965 ≤ 141426733) block2 block3

theorem join_1_0 : (twinPrimeSegment 141295661 141426733).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 141295661 ≤ 141361197)
    (by decide : 141361197 ≤ 141426733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 141295661 141426733).card = 510 := join_1_0

end S067C06
end Sude.GeneratedTwinScan
