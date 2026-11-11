import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106692653 106725421 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 106692653 106725421).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106692653 106725421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106725421 106758189 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 106725421 106758189).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106725421 106758189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106758189 106790957 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 106758189 106790957).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106758189 106790957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106790957 106823725 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 106790957 106823725).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106790957 106823725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 106692653 106758189).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 106692653 ≤ 106725421)
    (by decide : 106725421 ≤ 106758189) block0 block1

theorem join_0_1 : (twinPrimeSegment 106758189 106823725).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 106758189 ≤ 106790957)
    (by decide : 106790957 ≤ 106823725) block2 block3

theorem join_1_0 : (twinPrimeSegment 106692653 106823725).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 106692653 ≤ 106758189)
    (by decide : 106758189 ≤ 106823725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 106692653 106823725).card = 505 := join_1_0

end S050C14
end Sude.GeneratedTwinScan
