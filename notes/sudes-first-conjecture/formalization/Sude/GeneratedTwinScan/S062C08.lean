import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131072045 131104813 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 131072045 131104813).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131072045 131104813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131104813 131137581 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 131104813 131137581).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131104813 131137581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131137581 131170349 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 131137581 131170349).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131137581 131170349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131170349 131203117 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 131170349 131203117).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131170349 131203117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 131072045 131137581).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 131072045 ≤ 131104813)
    (by decide : 131104813 ≤ 131137581) block0 block1

theorem join_0_1 : (twinPrimeSegment 131137581 131203117).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 131137581 ≤ 131170349)
    (by decide : 131170349 ≤ 131203117) block2 block3

theorem join_1_0 : (twinPrimeSegment 131072045 131203117).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 131072045 ≤ 131137581)
    (by decide : 131137581 ≤ 131203117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 131072045 131203117).card = 485 := join_1_0

end S062C08
end Sude.GeneratedTwinScan
