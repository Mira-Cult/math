import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122945581 122978349 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 122945581 122978349).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122945581 122978349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122978349 123011117 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 122978349 123011117).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122978349 123011117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123011117 123043885 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 123011117 123043885).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123011117 123043885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123043885 123076653 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 123043885 123076653).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123043885 123076653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 122945581 123011117).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 122945581 ≤ 122978349)
    (by decide : 122978349 ≤ 123011117) block0 block1

theorem join_0_1 : (twinPrimeSegment 123011117 123076653).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 123011117 ≤ 123043885)
    (by decide : 123043885 ≤ 123076653) block2 block3

theorem join_1_0 : (twinPrimeSegment 122945581 123076653).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 122945581 ≤ 123011117)
    (by decide : 123011117 ≤ 123076653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 122945581 123076653).card = 501 := join_1_0

end S058C10
end Sude.GeneratedTwinScan
