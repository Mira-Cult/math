import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100007981 100040749 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 100007981 100040749).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100007981 100040749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100040749 100073517 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 100040749 100073517).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100040749 100073517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100073517 100106285 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 100073517 100106285).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100073517 100106285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100106285 100139053 = 158 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 100106285 100139053).card = 158 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100106285 100139053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 100007981 100073517).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 100007981 ≤ 100040749)
    (by decide : 100040749 ≤ 100073517) block0 block1

theorem join_0_1 : (twinPrimeSegment 100073517 100139053).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 100073517 ≤ 100106285)
    (by decide : 100106285 ≤ 100139053) block2 block3

theorem join_1_0 : (twinPrimeSegment 100007981 100139053).card = 516 := by
  simpa using combineTwinPrimeSegments (by decide : 100007981 ≤ 100073517)
    (by decide : 100073517 ≤ 100139053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 100007981 100139053).card = 516 := join_1_0

end S047C11
end Sude.GeneratedTwinScan
