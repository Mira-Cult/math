import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140771373 140804141 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 140771373 140804141).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140771373 140804141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140804141 140836909 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 140804141 140836909).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140804141 140836909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140836909 140869677 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 140836909 140869677).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140836909 140869677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140869677 140902445 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 140869677 140902445).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140869677 140902445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 140771373 140836909).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 140771373 ≤ 140804141)
    (by decide : 140804141 ≤ 140836909) block0 block1

theorem join_0_1 : (twinPrimeSegment 140836909 140902445).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 140836909 ≤ 140869677)
    (by decide : 140869677 ≤ 140902445) block2 block3

theorem join_1_0 : (twinPrimeSegment 140771373 140902445).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 140771373 ≤ 140836909)
    (by decide : 140836909 ≤ 140902445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 140771373 140902445).card = 462 := join_1_0

end S067C02
end Sude.GeneratedTwinScan
