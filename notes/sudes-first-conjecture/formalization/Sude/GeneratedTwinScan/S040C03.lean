import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84279341 84312109 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 84279341 84312109).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84279341 84312109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84312109 84344877 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 84312109 84344877).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84312109 84344877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84344877 84377645 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 84344877 84377645).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84344877 84377645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84377645 84410413 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 84377645 84410413).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84377645 84410413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 84279341 84344877).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 84279341 ≤ 84312109)
    (by decide : 84312109 ≤ 84344877) block0 block1

theorem join_0_1 : (twinPrimeSegment 84344877 84410413).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 84344877 ≤ 84377645)
    (by decide : 84377645 ≤ 84410413) block2 block3

theorem join_1_0 : (twinPrimeSegment 84279341 84410413).card = 518 := by
  simpa using combineTwinPrimeSegments (by decide : 84279341 ≤ 84344877)
    (by decide : 84344877 ≤ 84410413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 84279341 84410413).card = 518 := join_1_0

end S040C03
end Sude.GeneratedTwinScan
