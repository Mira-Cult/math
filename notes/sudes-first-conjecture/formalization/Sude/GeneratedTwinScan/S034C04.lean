import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71827501 71860269 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 71827501 71860269).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71827501 71860269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71860269 71893037 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 71860269 71893037).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71860269 71893037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71893037 71925805 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 71893037 71925805).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71893037 71925805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71925805 71958573 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 71925805 71958573).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71925805 71958573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 71827501 71893037).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 71827501 ≤ 71860269)
    (by decide : 71860269 ≤ 71893037) block0 block1

theorem join_0_1 : (twinPrimeSegment 71893037 71958573).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 71893037 ≤ 71925805)
    (by decide : 71925805 ≤ 71958573) block2 block3

theorem join_1_0 : (twinPrimeSegment 71827501 71958573).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 71827501 ≤ 71893037)
    (by decide : 71893037 ≤ 71958573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 71827501 71958573).card = 520 := join_1_0

end S034C04
end Sude.GeneratedTwinScan
