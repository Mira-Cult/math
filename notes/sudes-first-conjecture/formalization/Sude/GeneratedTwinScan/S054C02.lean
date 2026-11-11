import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113508397 113541165 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 113508397 113541165).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113508397 113541165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113541165 113573933 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 113541165 113573933).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113541165 113573933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113573933 113606701 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 113573933 113606701).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113573933 113606701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113606701 113639469 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 113606701 113639469).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113606701 113639469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 113508397 113573933).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 113508397 ≤ 113541165)
    (by decide : 113541165 ≤ 113573933) block0 block1

theorem join_0_1 : (twinPrimeSegment 113573933 113639469).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 113573933 ≤ 113606701)
    (by decide : 113606701 ≤ 113639469) block2 block3

theorem join_1_0 : (twinPrimeSegment 113508397 113639469).card = 527 := by
  simpa using combineTwinPrimeSegments (by decide : 113508397 ≤ 113573933)
    (by decide : 113573933 ≤ 113639469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 113508397 113639469).card = 527 := join_1_0

end S054C02
end Sude.GeneratedTwinScan
