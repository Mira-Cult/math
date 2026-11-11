import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96993325 97026093 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 96993325 97026093).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96993325 97026093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97026093 97058861 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 97026093 97058861).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97026093 97058861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97058861 97091629 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 97058861 97091629).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97058861 97091629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97091629 97124397 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 97091629 97124397).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97091629 97124397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 96993325 97058861).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 96993325 ≤ 97026093)
    (by decide : 97026093 ≤ 97058861) block0 block1

theorem join_0_1 : (twinPrimeSegment 97058861 97124397).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 97058861 ≤ 97091629)
    (by decide : 97091629 ≤ 97124397) block2 block3

theorem join_1_0 : (twinPrimeSegment 96993325 97124397).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 96993325 ≤ 97058861)
    (by decide : 97058861 ≤ 97124397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 96993325 97124397).card = 521 := join_1_0

end S046C04
end Sude.GeneratedTwinScan
