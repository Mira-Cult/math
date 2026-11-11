import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116260909 116293677 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 116260909 116293677).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116260909 116293677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116293677 116326445 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 116293677 116326445).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116293677 116326445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116326445 116359213 = 148 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 116326445 116359213).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116326445 116359213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116359213 116391981 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 116359213 116391981).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116359213 116391981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 116260909 116326445).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 116260909 ≤ 116293677)
    (by decide : 116293677 ≤ 116326445) block0 block1

theorem join_0_1 : (twinPrimeSegment 116326445 116391981).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 116326445 ≤ 116359213)
    (by decide : 116359213 ≤ 116391981) block2 block3

theorem join_1_0 : (twinPrimeSegment 116260909 116391981).card = 527 := by
  simpa using combineTwinPrimeSegments (by decide : 116260909 ≤ 116326445)
    (by decide : 116326445 ≤ 116391981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 116260909 116391981).card = 527 := join_1_0

end S055C07
end Sude.GeneratedTwinScan
