import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146407469 146440237 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 146407469 146440237).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146407469 146440237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146440237 146473005 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 146440237 146473005).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146440237 146473005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146473005 146505773 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 146473005 146505773).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146473005 146505773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146505773 146538541 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 146505773 146538541).card = 104 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146505773 146538541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 146407469 146473005).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 146407469 ≤ 146440237)
    (by decide : 146440237 ≤ 146473005) block0 block1

theorem join_0_1 : (twinPrimeSegment 146473005 146538541).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 146473005 ≤ 146505773)
    (by decide : 146505773 ≤ 146538541) block2 block3

theorem join_1_0 : (twinPrimeSegment 146407469 146538541).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 146407469 ≤ 146473005)
    (by decide : 146473005 ≤ 146538541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 146407469 146538541).card = 444 := join_1_0

end S069C13
end Sude.GeneratedTwinScan
