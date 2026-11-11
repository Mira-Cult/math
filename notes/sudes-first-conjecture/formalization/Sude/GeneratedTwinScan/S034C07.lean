import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72220717 72253485 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 72220717 72253485).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72220717 72253485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72253485 72286253 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 72253485 72286253).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72253485 72286253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72286253 72319021 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 72286253 72319021).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72286253 72319021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72319021 72351789 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 72319021 72351789).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72319021 72351789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 72220717 72286253).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 72220717 ≤ 72253485)
    (by decide : 72253485 ≤ 72286253) block0 block1

theorem join_0_1 : (twinPrimeSegment 72286253 72351789).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 72286253 ≤ 72319021)
    (by decide : 72319021 ≤ 72351789) block2 block3

theorem join_1_0 : (twinPrimeSegment 72220717 72351789).card = 566 := by
  simpa using combineTwinPrimeSegments (by decide : 72220717 ≤ 72286253)
    (by decide : 72286253 ≤ 72351789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 72220717 72351789).card = 566 := join_1_0

end S034C07
end Sude.GeneratedTwinScan
