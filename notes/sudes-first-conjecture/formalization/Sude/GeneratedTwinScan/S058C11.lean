import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123076653 123109421 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 123076653 123109421).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123076653 123109421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123109421 123142189 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 123109421 123142189).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123109421 123142189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123142189 123174957 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 123142189 123174957).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123142189 123174957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123174957 123207725 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 123174957 123207725).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123174957 123207725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 123076653 123142189).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 123076653 ≤ 123109421)
    (by decide : 123109421 ≤ 123142189) block0 block1

theorem join_0_1 : (twinPrimeSegment 123142189 123207725).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 123142189 ≤ 123174957)
    (by decide : 123174957 ≤ 123207725) block2 block3

theorem join_1_0 : (twinPrimeSegment 123076653 123207725).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 123076653 ≤ 123142189)
    (by decide : 123142189 ≤ 123207725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 123076653 123207725).card = 490 := join_1_0

end S058C11
end Sude.GeneratedTwinScan
