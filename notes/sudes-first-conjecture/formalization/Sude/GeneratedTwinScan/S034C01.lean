import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71434285 71467053 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 71434285 71467053).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71434285 71467053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71467053 71499821 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 71467053 71499821).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71467053 71499821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71499821 71532589 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 71499821 71532589).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71499821 71532589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71532589 71565357 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 71532589 71565357).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71532589 71565357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 71434285 71499821).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 71434285 ≤ 71467053)
    (by decide : 71467053 ≤ 71499821) block0 block1

theorem join_0_1 : (twinPrimeSegment 71499821 71565357).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 71499821 ≤ 71532589)
    (by decide : 71532589 ≤ 71565357) block2 block3

theorem join_1_0 : (twinPrimeSegment 71434285 71565357).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 71434285 ≤ 71499821)
    (by decide : 71499821 ≤ 71565357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 71434285 71565357).card = 505 := join_1_0

end S034C01
end Sude.GeneratedTwinScan
