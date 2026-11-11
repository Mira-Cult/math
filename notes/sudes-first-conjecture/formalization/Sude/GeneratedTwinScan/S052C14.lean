import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110886957 110919725 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 110886957 110919725).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110886957 110919725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110919725 110952493 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 110919725 110952493).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110919725 110952493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110952493 110985261 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 110952493 110985261).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110952493 110985261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110985261 111018029 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 110985261 111018029).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110985261 111018029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 110886957 110952493).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 110886957 ≤ 110919725)
    (by decide : 110919725 ≤ 110952493) block0 block1

theorem join_0_1 : (twinPrimeSegment 110952493 111018029).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 110952493 ≤ 110985261)
    (by decide : 110985261 ≤ 111018029) block2 block3

theorem join_1_0 : (twinPrimeSegment 110886957 111018029).card = 528 := by
  simpa using combineTwinPrimeSegments (by decide : 110886957 ≤ 110952493)
    (by decide : 110952493 ≤ 111018029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 110886957 111018029).card = 528 := join_1_0

end S052C14
end Sude.GeneratedTwinScan
