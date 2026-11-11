import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106430509 106463277 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 106430509 106463277).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106430509 106463277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106463277 106496045 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 106463277 106496045).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106463277 106496045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106496045 106528813 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 106496045 106528813).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106496045 106528813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106528813 106561581 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 106528813 106561581).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106528813 106561581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 106430509 106496045).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 106430509 ≤ 106463277)
    (by decide : 106463277 ≤ 106496045) block0 block1

theorem join_0_1 : (twinPrimeSegment 106496045 106561581).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 106496045 ≤ 106528813)
    (by decide : 106528813 ≤ 106561581) block2 block3

theorem join_1_0 : (twinPrimeSegment 106430509 106561581).card = 531 := by
  simpa using combineTwinPrimeSegments (by decide : 106430509 ≤ 106496045)
    (by decide : 106496045 ≤ 106561581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 106430509 106561581).card = 531 := join_1_0

end S050C12
end Sude.GeneratedTwinScan
