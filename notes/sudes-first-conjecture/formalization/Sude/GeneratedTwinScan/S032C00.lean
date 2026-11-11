import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67108909 67141677 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 67108909 67141677).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67108909 67141677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67141677 67174445 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 67141677 67174445).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67141677 67174445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67174445 67207213 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 67174445 67207213).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67174445 67207213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67207213 67239981 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 67207213 67239981).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67207213 67239981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 67108909 67174445).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 67141677)
    (by decide : 67141677 ≤ 67174445) block0 block1

theorem join_0_1 : (twinPrimeSegment 67174445 67239981).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 67174445 ≤ 67207213)
    (by decide : 67207213 ≤ 67239981) block2 block3

theorem join_1_0 : (twinPrimeSegment 67108909 67239981).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 67174445)
    (by decide : 67174445 ≤ 67239981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 67108909 67239981).card = 507 := join_1_0

end S032C00
end Sude.GeneratedTwinScan
