import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100139053 100171821 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 100139053 100171821).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100139053 100171821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100171821 100204589 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 100171821 100204589).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100171821 100204589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100204589 100237357 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 100204589 100237357).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100204589 100237357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100237357 100270125 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 100237357 100270125).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100237357 100270125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 100139053 100204589).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 100139053 ≤ 100171821)
    (by decide : 100171821 ≤ 100204589) block0 block1

theorem join_0_1 : (twinPrimeSegment 100204589 100270125).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 100204589 ≤ 100237357)
    (by decide : 100237357 ≤ 100270125) block2 block3

theorem join_1_0 : (twinPrimeSegment 100139053 100270125).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 100139053 ≤ 100204589)
    (by decide : 100204589 ≤ 100270125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 100139053 100270125).card = 504 := join_1_0

end S047C12
end Sude.GeneratedTwinScan
