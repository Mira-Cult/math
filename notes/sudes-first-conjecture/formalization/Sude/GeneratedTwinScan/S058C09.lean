import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122814509 122847277 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 122814509 122847277).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122814509 122847277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122847277 122880045 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 122847277 122880045).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122847277 122880045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122880045 122912813 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 122880045 122912813).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122880045 122912813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122912813 122945581 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 122912813 122945581).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122912813 122945581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 122814509 122880045).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 122814509 ≤ 122847277)
    (by decide : 122847277 ≤ 122880045) block0 block1

theorem join_0_1 : (twinPrimeSegment 122880045 122945581).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 122880045 ≤ 122912813)
    (by decide : 122912813 ≤ 122945581) block2 block3

theorem join_1_0 : (twinPrimeSegment 122814509 122945581).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 122814509 ≤ 122880045)
    (by decide : 122880045 ≤ 122945581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 122814509 122945581).card = 508 := join_1_0

end S058C09
end Sude.GeneratedTwinScan
