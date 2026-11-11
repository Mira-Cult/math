import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145096749 145129517 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 145096749 145129517).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145096749 145129517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145129517 145162285 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 145129517 145162285).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145129517 145162285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145162285 145195053 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 145162285 145195053).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145162285 145195053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145195053 145227821 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 145195053 145227821).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145195053 145227821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 145096749 145162285).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 145096749 ≤ 145129517)
    (by decide : 145129517 ≤ 145162285) block0 block1

theorem join_0_1 : (twinPrimeSegment 145162285 145227821).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 145162285 ≤ 145195053)
    (by decide : 145195053 ≤ 145227821) block2 block3

theorem join_1_0 : (twinPrimeSegment 145096749 145227821).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 145096749 ≤ 145162285)
    (by decide : 145162285 ≤ 145227821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 145096749 145227821).card = 489 := join_1_0

end S069C03
end Sude.GeneratedTwinScan
