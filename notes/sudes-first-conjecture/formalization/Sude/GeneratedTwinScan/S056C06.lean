import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118226989 118259757 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 118226989 118259757).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118226989 118259757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118259757 118292525 = 150 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 118259757 118292525).card = 150 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118259757 118292525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118292525 118325293 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 118292525 118325293).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118292525 118325293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118325293 118358061 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 118325293 118358061).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118325293 118358061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 118226989 118292525).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 118226989 ≤ 118259757)
    (by decide : 118259757 ≤ 118292525) block0 block1

theorem join_0_1 : (twinPrimeSegment 118292525 118358061).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 118292525 ≤ 118325293)
    (by decide : 118325293 ≤ 118358061) block2 block3

theorem join_1_0 : (twinPrimeSegment 118226989 118358061).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 118226989 ≤ 118292525)
    (by decide : 118292525 ≤ 118358061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 118226989 118358061).card = 513 := join_1_0

end S056C06
end Sude.GeneratedTwinScan
