import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126484525 126517293 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 126484525 126517293).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126484525 126517293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126517293 126550061 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 126517293 126550061).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126517293 126550061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126550061 126582829 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 126550061 126582829).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126550061 126582829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126582829 126615597 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 126582829 126615597).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126582829 126615597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 126484525 126550061).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 126484525 ≤ 126517293)
    (by decide : 126517293 ≤ 126550061) block0 block1

theorem join_0_1 : (twinPrimeSegment 126550061 126615597).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 126550061 ≤ 126582829)
    (by decide : 126582829 ≤ 126615597) block2 block3

theorem join_1_0 : (twinPrimeSegment 126484525 126615597).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 126484525 ≤ 126550061)
    (by decide : 126550061 ≤ 126615597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 126484525 126615597).card = 479 := join_1_0

end S060C05
end Sude.GeneratedTwinScan
