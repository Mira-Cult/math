import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120455213 120487981 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 120455213 120487981).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120455213 120487981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120487981 120520749 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 120487981 120520749).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120487981 120520749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120520749 120553517 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 120520749 120553517).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120520749 120553517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120553517 120586285 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 120553517 120586285).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120553517 120586285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 120455213 120520749).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 120455213 ≤ 120487981)
    (by decide : 120487981 ≤ 120520749) block0 block1

theorem join_0_1 : (twinPrimeSegment 120520749 120586285).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 120520749 ≤ 120553517)
    (by decide : 120553517 ≤ 120586285) block2 block3

theorem join_1_0 : (twinPrimeSegment 120455213 120586285).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 120455213 ≤ 120520749)
    (by decide : 120520749 ≤ 120586285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 120455213 120586285).card = 498 := join_1_0

end S057C07
end Sude.GeneratedTwinScan
