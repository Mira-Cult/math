import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149159981 149192749 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 149159981 149192749).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149159981 149192749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149192749 149225517 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 149192749 149225517).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149192749 149225517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149225517 149258285 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 149225517 149258285).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149225517 149258285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149258285 149291053 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 149258285 149291053).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149258285 149291053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 149159981 149225517).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 149159981 ≤ 149192749)
    (by decide : 149192749 ≤ 149225517) block0 block1

theorem join_0_1 : (twinPrimeSegment 149225517 149291053).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 149225517 ≤ 149258285)
    (by decide : 149258285 ≤ 149291053) block2 block3

theorem join_1_0 : (twinPrimeSegment 149159981 149291053).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 149159981 ≤ 149225517)
    (by decide : 149225517 ≤ 149291053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 149159981 149291053).card = 503 := join_1_0

end S071C02
end Sude.GeneratedTwinScan
