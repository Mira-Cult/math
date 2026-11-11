import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75366445 75399213 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 75366445 75399213).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75366445 75399213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75399213 75431981 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 75399213 75431981).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75399213 75431981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75431981 75464749 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 75431981 75464749).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75431981 75464749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75464749 75497517 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 75464749 75497517).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75464749 75497517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 75366445 75431981).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 75366445 ≤ 75399213)
    (by decide : 75399213 ≤ 75431981) block0 block1

theorem join_0_1 : (twinPrimeSegment 75431981 75497517).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 75431981 ≤ 75464749)
    (by decide : 75464749 ≤ 75497517) block2 block3

theorem join_1_0 : (twinPrimeSegment 75366445 75497517).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 75366445 ≤ 75431981)
    (by decide : 75431981 ≤ 75497517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 75366445 75497517).card = 520 := join_1_0

end S035C15
end Sude.GeneratedTwinScan
