import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144965677 144998445 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 144965677 144998445).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144965677 144998445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144998445 145031213 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 144998445 145031213).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144998445 145031213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145031213 145063981 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 145031213 145063981).card = 104 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145031213 145063981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145063981 145096749 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 145063981 145096749).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145063981 145096749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 144965677 145031213).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 144965677 ≤ 144998445)
    (by decide : 144998445 ≤ 145031213) block0 block1

theorem join_0_1 : (twinPrimeSegment 145031213 145096749).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 145031213 ≤ 145063981)
    (by decide : 145063981 ≤ 145096749) block2 block3

theorem join_1_0 : (twinPrimeSegment 144965677 145096749).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 144965677 ≤ 145031213)
    (by decide : 145031213 ≤ 145096749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 144965677 145096749).card = 485 := join_1_0

end S069C02
end Sude.GeneratedTwinScan
