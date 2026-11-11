import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113639469 113672237 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 113639469 113672237).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113639469 113672237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113672237 113705005 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 113672237 113705005).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113672237 113705005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113705005 113737773 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 113705005 113737773).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113705005 113737773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113737773 113770541 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 113737773 113770541).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113737773 113770541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 113639469 113705005).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 113639469 ≤ 113672237)
    (by decide : 113672237 ≤ 113705005) block0 block1

theorem join_0_1 : (twinPrimeSegment 113705005 113770541).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 113705005 ≤ 113737773)
    (by decide : 113737773 ≤ 113770541) block2 block3

theorem join_1_0 : (twinPrimeSegment 113639469 113770541).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 113639469 ≤ 113705005)
    (by decide : 113705005 ≤ 113770541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 113639469 113770541).card = 494 := join_1_0

end S054C03
end Sude.GeneratedTwinScan
