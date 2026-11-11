import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64356397 64389165 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 64356397 64389165).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64356397 64389165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64389165 64421933 = 151 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 64389165 64421933).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64389165 64421933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64421933 64454701 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 64421933 64454701).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64421933 64454701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64454701 64487469 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 64454701 64487469).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64454701 64487469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 64356397 64421933).card = 297 := by
  simpa using combineTwinPrimeSegments (by decide : 64356397 ≤ 64389165)
    (by decide : 64389165 ≤ 64421933) block0 block1

theorem join_0_1 : (twinPrimeSegment 64421933 64487469).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 64421933 ≤ 64454701)
    (by decide : 64454701 ≤ 64487469) block2 block3

theorem join_1_0 : (twinPrimeSegment 64356397 64487469).card = 547 := by
  simpa using combineTwinPrimeSegments (by decide : 64356397 ≤ 64421933)
    (by decide : 64421933 ≤ 64487469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 64356397 64487469).card = 547 := join_1_0

end S030C11
end Sude.GeneratedTwinScan
