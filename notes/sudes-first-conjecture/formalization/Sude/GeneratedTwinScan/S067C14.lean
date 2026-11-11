import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142344237 142377005 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 142344237 142377005).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142344237 142377005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142377005 142409773 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 142377005 142409773).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142377005 142409773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142409773 142442541 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 142409773 142442541).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142409773 142442541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142442541 142475309 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 142442541 142475309).card = 105 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142442541 142475309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 142344237 142409773).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 142344237 ≤ 142377005)
    (by decide : 142377005 ≤ 142409773) block0 block1

theorem join_0_1 : (twinPrimeSegment 142409773 142475309).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 142409773 ≤ 142442541)
    (by decide : 142442541 ≤ 142475309) block2 block3

theorem join_1_0 : (twinPrimeSegment 142344237 142475309).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 142344237 ≤ 142409773)
    (by decide : 142409773 ≤ 142475309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 142344237 142475309).card = 486 := join_1_0

end S067C14
end Sude.GeneratedTwinScan
