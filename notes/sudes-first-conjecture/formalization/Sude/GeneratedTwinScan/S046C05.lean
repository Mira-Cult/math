import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97124397 97157165 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 97124397 97157165).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97124397 97157165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97157165 97189933 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 97157165 97189933).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97157165 97189933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97189933 97222701 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 97189933 97222701).card = 105 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97189933 97222701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97222701 97255469 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 97222701 97255469).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97222701 97255469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 97124397 97189933).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 97124397 ≤ 97157165)
    (by decide : 97157165 ≤ 97189933) block0 block1

theorem join_0_1 : (twinPrimeSegment 97189933 97255469).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 97189933 ≤ 97222701)
    (by decide : 97222701 ≤ 97255469) block2 block3

theorem join_1_0 : (twinPrimeSegment 97124397 97255469).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 97124397 ≤ 97189933)
    (by decide : 97189933 ≤ 97255469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 97124397 97255469).card = 457 := join_1_0

end S046C05
end Sude.GeneratedTwinScan
