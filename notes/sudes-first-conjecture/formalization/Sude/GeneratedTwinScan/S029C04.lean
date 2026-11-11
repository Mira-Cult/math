import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61341741 61374509 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 61341741 61374509).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61341741 61374509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61374509 61407277 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 61374509 61407277).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61374509 61407277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61407277 61440045 = 152 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 61407277 61440045).card = 152 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61407277 61440045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61440045 61472813 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 61440045 61472813).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61440045 61472813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 61341741 61407277).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 61341741 ≤ 61374509)
    (by decide : 61374509 ≤ 61407277) block0 block1

theorem join_0_1 : (twinPrimeSegment 61407277 61472813).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 61407277 ≤ 61440045)
    (by decide : 61440045 ≤ 61472813) block2 block3

theorem join_1_0 : (twinPrimeSegment 61341741 61472813).card = 528 := by
  simpa using combineTwinPrimeSegments (by decide : 61341741 ≤ 61407277)
    (by decide : 61407277 ≤ 61472813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 61341741 61472813).card = 528 := join_1_0

end S029C04
end Sude.GeneratedTwinScan
