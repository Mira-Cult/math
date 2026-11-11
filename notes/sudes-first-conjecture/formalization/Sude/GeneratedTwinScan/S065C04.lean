import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136839213 136871981 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 136839213 136871981).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136839213 136871981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136871981 136904749 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 136871981 136904749).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136871981 136904749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136904749 136937517 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 136904749 136937517).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136904749 136937517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136937517 136970285 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 136937517 136970285).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136937517 136970285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 136839213 136904749).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 136839213 ≤ 136871981)
    (by decide : 136871981 ≤ 136904749) block0 block1

theorem join_0_1 : (twinPrimeSegment 136904749 136970285).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 136904749 ≤ 136937517)
    (by decide : 136937517 ≤ 136970285) block2 block3

theorem join_1_0 : (twinPrimeSegment 136839213 136970285).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 136839213 ≤ 136904749)
    (by decide : 136904749 ≤ 136970285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 136839213 136970285).card = 484 := join_1_0

end S065C04
end Sude.GeneratedTwinScan
