import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69861421 69894189 = 154 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 69861421 69894189).card = 154 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69861421 69894189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69894189 69926957 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 69894189 69926957).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69894189 69926957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69926957 69959725 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 69926957 69959725).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69926957 69959725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69959725 69992493 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 69959725 69992493).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69959725 69992493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 69861421 69926957).card = 290 := by
  simpa using combineTwinPrimeSegments (by decide : 69861421 ≤ 69894189)
    (by decide : 69894189 ≤ 69926957) block0 block1

theorem join_0_1 : (twinPrimeSegment 69926957 69992493).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 69926957 ≤ 69959725)
    (by decide : 69959725 ≤ 69992493) block2 block3

theorem join_1_0 : (twinPrimeSegment 69861421 69992493).card = 557 := by
  simpa using combineTwinPrimeSegments (by decide : 69861421 ≤ 69926957)
    (by decide : 69926957 ≤ 69992493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 69861421 69992493).card = 557 := join_1_0

end S033C05
end Sude.GeneratedTwinScan
