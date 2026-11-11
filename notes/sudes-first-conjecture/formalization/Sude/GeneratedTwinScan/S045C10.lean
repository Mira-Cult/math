import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95682605 95715373 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 95682605 95715373).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95682605 95715373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95715373 95748141 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 95715373 95748141).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95715373 95748141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95748141 95780909 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 95748141 95780909).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95748141 95780909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95780909 95813677 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 95780909 95813677).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95780909 95813677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 95682605 95748141).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 95682605 ≤ 95715373)
    (by decide : 95715373 ≤ 95748141) block0 block1

theorem join_0_1 : (twinPrimeSegment 95748141 95813677).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 95748141 ≤ 95780909)
    (by decide : 95780909 ≤ 95813677) block2 block3

theorem join_1_0 : (twinPrimeSegment 95682605 95813677).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 95682605 ≤ 95748141)
    (by decide : 95748141 ≤ 95813677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 95682605 95813677).card = 522 := join_1_0

end S045C10
end Sude.GeneratedTwinScan
