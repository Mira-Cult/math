import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110362669 110395437 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 110362669 110395437).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110362669 110395437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110395437 110428205 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 110395437 110428205).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110395437 110428205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110428205 110460973 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 110428205 110460973).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110428205 110460973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110460973 110493741 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 110460973 110493741).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110460973 110493741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 110362669 110428205).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 110362669 ≤ 110395437)
    (by decide : 110395437 ≤ 110428205) block0 block1

theorem join_0_1 : (twinPrimeSegment 110428205 110493741).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 110428205 ≤ 110460973)
    (by decide : 110460973 ≤ 110493741) block2 block3

theorem join_1_0 : (twinPrimeSegment 110362669 110493741).card = 529 := by
  simpa using combineTwinPrimeSegments (by decide : 110362669 ≤ 110428205)
    (by decide : 110428205 ≤ 110493741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 110362669 110493741).card = 529 := join_1_0

end S052C10
end Sude.GeneratedTwinScan
