import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69468205 69500973 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 69468205 69500973).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69468205 69500973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69500973 69533741 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 69500973 69533741).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69500973 69533741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69533741 69566509 = 154 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 69533741 69566509).card = 154 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69533741 69566509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69566509 69599277 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 69566509 69599277).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69566509 69599277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 69468205 69533741).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 69468205 ≤ 69500973)
    (by decide : 69500973 ≤ 69533741) block0 block1

theorem join_0_1 : (twinPrimeSegment 69533741 69599277).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 69533741 ≤ 69566509)
    (by decide : 69566509 ≤ 69599277) block2 block3

theorem join_1_0 : (twinPrimeSegment 69468205 69599277).card = 556 := by
  simpa using combineTwinPrimeSegments (by decide : 69468205 ≤ 69533741)
    (by decide : 69533741 ≤ 69599277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 69468205 69599277).card = 556 := join_1_0

end S033C02
end Sude.GeneratedTwinScan
