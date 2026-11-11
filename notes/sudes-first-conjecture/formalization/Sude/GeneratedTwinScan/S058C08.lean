import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122683437 122716205 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 122683437 122716205).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122683437 122716205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122716205 122748973 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 122716205 122748973).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122716205 122748973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122748973 122781741 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 122748973 122781741).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122748973 122781741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122781741 122814509 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 122781741 122814509).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122781741 122814509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 122683437 122748973).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 122683437 ≤ 122716205)
    (by decide : 122716205 ≤ 122748973) block0 block1

theorem join_0_1 : (twinPrimeSegment 122748973 122814509).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 122748973 ≤ 122781741)
    (by decide : 122781741 ≤ 122814509) block2 block3

theorem join_1_0 : (twinPrimeSegment 122683437 122814509).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 122683437 ≤ 122748973)
    (by decide : 122748973 ≤ 122814509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 122683437 122814509).card = 517 := join_1_0

end S058C08
end Sude.GeneratedTwinScan
