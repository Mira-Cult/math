import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101056557 101089325 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 101056557 101089325).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101056557 101089325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101089325 101122093 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 101089325 101122093).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101089325 101122093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101122093 101154861 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 101122093 101154861).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101122093 101154861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101154861 101187629 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 101154861 101187629).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101154861 101187629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 101056557 101122093).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 101056557 ≤ 101089325)
    (by decide : 101089325 ≤ 101122093) block0 block1

theorem join_0_1 : (twinPrimeSegment 101122093 101187629).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 101122093 ≤ 101154861)
    (by decide : 101154861 ≤ 101187629) block2 block3

theorem join_1_0 : (twinPrimeSegment 101056557 101187629).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 101056557 ≤ 101122093)
    (by decide : 101122093 ≤ 101187629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 101056557 101187629).card = 502 := join_1_0

end S048C03
end Sude.GeneratedTwinScan
