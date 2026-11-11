import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110493741 110526509 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 110493741 110526509).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110493741 110526509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110526509 110559277 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 110526509 110559277).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110526509 110559277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110559277 110592045 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 110559277 110592045).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110559277 110592045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110592045 110624813 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 110592045 110624813).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110592045 110624813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 110493741 110559277).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 110493741 ≤ 110526509)
    (by decide : 110526509 ≤ 110559277) block0 block1

theorem join_0_1 : (twinPrimeSegment 110559277 110624813).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 110559277 ≤ 110592045)
    (by decide : 110592045 ≤ 110624813) block2 block3

theorem join_1_0 : (twinPrimeSegment 110493741 110624813).card = 519 := by
  simpa using combineTwinPrimeSegments (by decide : 110493741 ≤ 110559277)
    (by decide : 110559277 ≤ 110624813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 110493741 110624813).card = 519 := join_1_0

end S052C11
end Sude.GeneratedTwinScan
