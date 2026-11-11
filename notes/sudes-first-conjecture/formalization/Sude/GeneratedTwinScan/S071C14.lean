import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150732845 150765613 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 150732845 150765613).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150732845 150765613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150765613 150798381 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 150765613 150798381).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150765613 150798381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150798381 150831149 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 150798381 150831149).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150798381 150831149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150831149 150863917 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 150831149 150863917).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150831149 150863917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 150732845 150798381).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 150732845 ≤ 150765613)
    (by decide : 150765613 ≤ 150798381) block0 block1

theorem join_0_1 : (twinPrimeSegment 150798381 150863917).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 150798381 ≤ 150831149)
    (by decide : 150831149 ≤ 150863917) block2 block3

theorem join_1_0 : (twinPrimeSegment 150732845 150863917).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 150732845 ≤ 150798381)
    (by decide : 150798381 ≤ 150863917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 150732845 150863917).card = 497 := join_1_0

end S071C14
end Sude.GeneratedTwinScan
