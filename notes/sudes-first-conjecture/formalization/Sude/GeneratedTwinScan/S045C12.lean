import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95944749 95977517 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 95944749 95977517).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95944749 95977517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95977517 96010285 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 95977517 96010285).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95977517 96010285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96010285 96043053 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 96010285 96043053).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96010285 96043053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96043053 96075821 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 96043053 96075821).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96043053 96075821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 95944749 96010285).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 95944749 ≤ 95977517)
    (by decide : 95977517 ≤ 96010285) block0 block1

theorem join_0_1 : (twinPrimeSegment 96010285 96075821).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 96010285 ≤ 96043053)
    (by decide : 96043053 ≤ 96075821) block2 block3

theorem join_1_0 : (twinPrimeSegment 95944749 96075821).card = 523 := by
  simpa using combineTwinPrimeSegments (by decide : 95944749 ≤ 96010285)
    (by decide : 96010285 ≤ 96075821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 95944749 96075821).card = 523 := join_1_0

end S045C12
end Sude.GeneratedTwinScan
