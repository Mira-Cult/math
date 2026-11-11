import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130285613 130318381 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 130285613 130318381).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130285613 130318381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130318381 130351149 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 130318381 130351149).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130318381 130351149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130351149 130383917 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 130351149 130383917).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130351149 130383917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130383917 130416685 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 130383917 130416685).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130383917 130416685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 130285613 130351149).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 130285613 ≤ 130318381)
    (by decide : 130318381 ≤ 130351149) block0 block1

theorem join_0_1 : (twinPrimeSegment 130351149 130416685).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 130351149 ≤ 130383917)
    (by decide : 130383917 ≤ 130416685) block2 block3

theorem join_1_0 : (twinPrimeSegment 130285613 130416685).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 130285613 ≤ 130351149)
    (by decide : 130351149 ≤ 130416685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 130285613 130416685).card = 480 := join_1_0

end S062C02
end Sude.GeneratedTwinScan
