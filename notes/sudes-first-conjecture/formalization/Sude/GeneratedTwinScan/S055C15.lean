import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117309485 117342253 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 117309485 117342253).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117309485 117342253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117342253 117375021 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 117342253 117375021).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117342253 117375021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117375021 117407789 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 117375021 117407789).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117375021 117407789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117407789 117440557 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 117407789 117440557).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117407789 117440557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 117309485 117375021).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 117309485 ≤ 117342253)
    (by decide : 117342253 ≤ 117375021) block0 block1

theorem join_0_1 : (twinPrimeSegment 117375021 117440557).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 117375021 ≤ 117407789)
    (by decide : 117407789 ≤ 117440557) block2 block3

theorem join_1_0 : (twinPrimeSegment 117309485 117440557).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 117309485 ≤ 117375021)
    (by decide : 117375021 ≤ 117440557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 117309485 117440557).card = 512 := join_1_0

end S055C15
end Sude.GeneratedTwinScan
