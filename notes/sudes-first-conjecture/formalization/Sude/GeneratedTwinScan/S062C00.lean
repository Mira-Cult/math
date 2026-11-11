import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130023469 130056237 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 130023469 130056237).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130023469 130056237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130056237 130089005 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 130056237 130089005).card = 101 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130056237 130089005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130089005 130121773 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 130089005 130121773).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130089005 130121773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130121773 130154541 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 130121773 130154541).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130121773 130154541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 130023469 130089005).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 130023469 ≤ 130056237)
    (by decide : 130056237 ≤ 130089005) block0 block1

theorem join_0_1 : (twinPrimeSegment 130089005 130154541).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 130089005 ≤ 130121773)
    (by decide : 130121773 ≤ 130154541) block2 block3

theorem join_1_0 : (twinPrimeSegment 130023469 130154541).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 130023469 ≤ 130089005)
    (by decide : 130089005 ≤ 130154541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 130023469 130154541).card = 467 := join_1_0

end S062C00
end Sude.GeneratedTwinScan
